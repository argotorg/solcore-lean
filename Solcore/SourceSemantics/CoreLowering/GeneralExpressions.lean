import Solcore.SourceSemantics.CoreLowering.GeneralHeap
import Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions
import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Scalar/product expression correspondence over a mapped heap that may also
contain administrative function cells. The existing structural compilation
certificates are reused. Exact temporary-binder insertion follows from the
restricted Core expression syntax, without a first-order store premise. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem appendContext {context : Core.Context} {expression : Core.Expr} {type : Core.Ty}
    (typed : Core.HasType context expression type) (administrative : Core.Context) :
    Core.HasType (context ++ administrative) expression type := by
  have respects : Core.Renaming.Respects Core.Renaming.id context (context ++ administrative) := by
    intro index foundType found
    change (context ++ administrative)[index]? = some foundType
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  simpa using typed.rename respects

private theorem success_readOnly {expression : Core.Expr} (restricted : Core.ReadOnly.Expression expression) :
    Core.ReadOnly.Expression (Core.LanguageResult.success expression) := .inRight restricted

private theorem bind_readOnly {computation body : Core.Expr} (type : Core.Ty)
    (computationRestricted : Core.ReadOnly.Expression computation) (bodyRestricted : Core.ReadOnly.Expression body) :
    Core.ReadOnly.Expression (Core.LanguageResult.bind type computation body) :=
  .caseE computationRestricted (.inLeft .var) bodyRestricted

private theorem pair_readOnly {left right : Core.Expr} (leftType rightType : Core.Ty)
    (leftRestricted : Core.ReadOnly.Expression left) (rightRestricted : Core.ReadOnly.Expression right) :
    Core.ReadOnly.Expression (Core.LocalSequence.pair leftType rightType left right) :=
  bind_readOnly _ leftRestricted (bind_readOnly _ (rightRestricted.weakenAt 0) (.inRight (.pair .var .var)))

private theorem choose_readOnly {condition thenBranch elseBranch : Core.Expr} (type : Core.Ty)
    (conditionRestricted : Core.ReadOnly.Expression condition)
    (thenRestricted : Core.ReadOnly.Expression thenBranch) (elseRestricted : Core.ReadOnly.Expression elseBranch) :
    Core.ReadOnly.Expression (Core.LocalControl.choose type condition thenBranch elseBranch) :=
  bind_readOnly _ conditionRestricted (.ifE .var (thenRestricted.weakenAt 0) (elseRestricted.weakenAt 0))

namespace Control

open ControlExpressions

theorem readOnly {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth) : Core.ReadOnly.Expression code := by
  induction tree with
  | unit => exact .inRight .unit
  | bool => exact .inRight .bool
  | word => exact .inRight .word
  | localRead => exact .caseE (.loadCell .var) (.inLeft .word) (.inRight .var)
  | group _ _ _ ih => exact ih
  | pair _ _ _ _ left right => exact pair_readOnly _ _ left right
  | conditional _ _ _ _ _ condition thenBranch elseBranch => exact choose_readOnly _ condition thenBranch elseBranch

private theorem map_root
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

theorem preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
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
      obtain ⟨location, target, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have cellType := related.types.source_unique metadata.types
      let site : ReadSite source scope id type := {
        node, binder, name, index, contains := metadata.contains, form, owner := owned
        requirements := metadata.requirements, coercions := metadata.coercions
        slot, types := metadata.types
      }
      cases related with
      | uninitialized types =>
          refine ⟨_, _, .fault ?_, .uninitialized id location (.localRead site lookup read cellType rfl rfl),
            Core.OptionalCell.read_failure (reasonAt id) (.var coreLookup) coreRead⟩
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .localUninitialized (owned := []) rfl lookup read rfl rfl types.not_mapping
      | initialized value =>
          refine ⟨_, _, .value ?_, .value value rfl,
            Core.OptionalCell.read_success (reasonAt id) (.var coreLookup) coreRead⟩
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]
            exact .local rfl lookup read rfl rfl
          · rw [metadata.coercions]; exact .nil
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, map_root related (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
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
              have weakened := (readOnly rightTree).evaluation_weakenAt_zero rightCore (SourceStagedValue.toCore leftValue)
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
                  have shifted := (readOnly thenTree).evaluation_weakenAt_zero branchCore (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .thenBranch metadata form conditionSource trace),
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
                  have shifted := (readOnly elseTree).evaluation_weakenAt_zero branchCore (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .elseBranch metadata form conditionSource trace),
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


theorem lowerExpression_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact preserves tree program context evidence environments heaps

/-- Completed runs agree even when the unmapped cells contain closures.
Only the finite expression grammar is covered. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreControl.lowerExpressionWithReasons fuel source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered.expression =
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
  refine ⟨Core.infer_complete (appendContext (ControlExpressions.lowerExpression_hasType unique accepted) administrativeContext),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Control

namespace Primitive

open PrimitiveExpressions

private theorem strictBody_readOnly (operator : Syntax.BinaryOp) :
    Core.ReadOnly.Expression (SourceCorePrimitive.strictBinaryBody operator) := by
  cases operator <;> first | exact .binary .var .var | exact .unary (.binary .var .var) | exact .ifE .var .var .bool | exact .ifE .var .bool .var

private theorem binary_readOnly {left right : Core.Expr} (operator : Syntax.BinaryOp)
    (leftRestricted : Core.ReadOnly.Expression left) (rightRestricted : Core.ReadOnly.Expression right) :
    Core.ReadOnly.Expression (SourceCorePrimitive.binary operator left right) := by
  cases operator <;> first
    | exact choose_readOnly _ leftRestricted rightRestricted (.inRight .bool)
    | exact choose_readOnly _ leftRestricted (.inRight .bool) rightRestricted
    | exact bind_readOnly _ leftRestricted
        (bind_readOnly _ (rightRestricted.weakenAt 0) (success_readOnly (strictBody_readOnly _)))

theorem readOnly {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth) : Core.ReadOnly.Expression code := by
  induction tree with
  | control tree => exact Control.readOnly tree
  | integerLiteral => exact .inRight .word
  | unary _ _ _ _ operand => exact bind_readOnly _ operand (.inRight (.unary .var))
  | binary operator _ _ _ _ left right => exact binary_readOnly operator left right
  | group _ _ _ ih => exact ih
  | pair _ _ _ _ left right => exact pair_readOnly _ _ left right
  | conditional _ _ _ _ _ condition thenBranch elseBranch => exact choose_readOnly _ condition thenBranch elseBranch

private theorem map_root
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

private theorem binary_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue rightValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (evaluateRight : Dynamic.EvaluatesRightOperand operator leftValue)
    (rightSource : Dynamic.ExpressionEvaluates program context evidence source environment heap right rightValue heap)
    (applied : Dynamic.BinaryPrimitiveApplies operator leftValue rightValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryEvaluateRight (owned := []) rfl leftSource evaluateRight rightSource (.primitive applied)
  · rw [metadata.coercions]; exact .nil

private theorem shortCircuit_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (circuit : Dynamic.ShortCircuits operator leftValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryShortCircuit (owned := []) rfl leftSource circuit rfl
  · rw [metadata.coercions]; exact .nil


theorem preserves {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | control tree =>
      obtain ⟨outcome, value, sourceEvaluation, related, coreEvaluation⟩ :=
        Control.preserves tree program context evidence environments heaps
      refine ⟨outcome, value, sourceEvaluation, ?_, coreEvaluation⟩
      cases related with
      | value staged typed => exact .value staged typed
      | uninitialized site location provenance => exact .uninitialized site location (.control provenance)
  | @integerLiteral id node literal resolution metadata form =>
      have proves : RequirementProves context resolution.requirement (ProgramSignatures.builtinIntPredicate .word) := by
        obtain ⟨solved, member, identifier, predicate⟩ := metadata.requirement
        have contains : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
        exact ⟨solved, ⟨contains, identifier⟩, predicate, valid.valid.entriesValid solved contains⟩
      have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution
          (.word (Core.Word.ofNatModulo resolution.rawValue)) := by
        cases resolution with
        | mk raw target requirement =>
            have targetEq := metadata.target
            dsimp only at targetEq
            subst target
            exact .word metadata.meaning proves
      refine ⟨_, _, .value ?_, .value (.word _) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .integerLiteral rfl constructs
      · rw [metadata.coercions]; exact .nil
  | @unary id operand node operandCode operandDepth operator metadata form child ih =>
      obtain ⟨outcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ := ih
      cases related with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.unary metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalPrimitiveResults.unary_failure coreEvaluation⟩
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨result, resultTyped, sourceApplied, coreApplied⟩ := unary_value operator staged typed
              refine ⟨_, _, .value ?_, .value result resultTyped,
                Core.LocalPrimitiveResults.unary_success coreEvaluation coreApplied⟩
              apply Dynamic.ExpressionEvaluates.intro metadata.contains
              · rw [form, metadata.requirements, metadata.coercions]
                exact .unary (owned := []) rfl sourceEvaluation (.primitive sourceApplied)
              · rw [metadata.coercions]; exact .nil
  | @binary id left right node leftCode rightCode leftDepth rightDepth operator metadata form
      leftTree rightTree leftIH rightIH =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftIH
      cases leftRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.binaryLeft metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            binary_left_failure leftCore⟩
      | value leftValue leftTyped =>
          cases leftSource with
          | value leftSource =>
              by_cases strict : Dynamic.StrictBinaryOperator operator
              · have leftWord := word_of_type leftValue (leftTyped.trans (strict_operand_word strict))
                obtain ⟨leftWord, rfl⟩ := leftWord
                obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.word leftWord)
                cases rightRelated with
                | uninitialized site location provenance =>
                    have propagated := UninitializedAt.binaryRight metadata form leftSource (.strict strict) provenance
                    refine ⟨_, _, .fault propagated.faults, .uninitialized site location propagated, ?_⟩
                    rw [binary_strict strict]
                    exact Core.LocalPrimitiveResults.binaryWith_right_failure leftCore shifted
                | value rightValue rightTyped =>
                    cases rightSource with
                    | value rightSource =>
                        obtain ⟨rightWord, rfl⟩ := word_of_type rightValue (rightTyped.trans (strict_operand_word strict))
                        obtain ⟨result, resultTyped, applied, bodyEvaluation⟩ := strict_binary_value strict leftWord rightWord
                        refine ⟨_, _, .value (binary_evaluates metadata form leftSource (.strict strict) rightSource applied),
                          .value result resultTyped, ?_⟩
                        rw [binary_strict strict]
                        exact Core.LocalPrimitiveResults.binaryWith_success leftCore shifted (bodyEvaluation _ _)
              · rcases binary_nonstrict strict with isAnd | isOr
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | false =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .andFalse),
                        .value (.bool false) rfl, Core.LocalPrimitiveResults.logicalAnd_shortCircuit leftCore⟩
                  | true =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.bool true)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .andTrue provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .andTrue rightSource
                                (.logicalAnd true rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | true =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .orTrue),
                        .value (.bool true) rfl, Core.LocalPrimitiveResults.logicalOr_shortCircuit leftCore⟩
                  | false =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := (readOnly rightTree).evaluation_weakenAt_zero rightCore (.bool false)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .orFalse provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .orFalse rightSource
                                (.logicalOr false rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, map_root related (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
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
              have weakened := (readOnly rightTree).evaluation_weakenAt_zero rightCore
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
                  have shifted := (readOnly thenTree).evaluation_weakenAt_zero branchCore (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .thenBranch metadata form conditionSource trace),
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
                  have shifted := (readOnly elseTree).evaluation_weakenAt_zero branchCore (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    map_root branchRelated (fun _ _ trace => .elseBranch metadata form conditionSource trace),
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



theorem lowerExpression_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact preserves tree program context evidence valid environments heaps

/-- All completed runs agree with the derived source outcome, including exact
executed read reasons. Sufficient fuel follows from this finite expression
grammar; no unrestricted source normalization or fault completeness is claimed. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence valid environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (appendContext (PrimitiveExpressions.lowerExpression_hasType unique accepted) administrativeContext),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Primitive

namespace Basic

/-- Constant read reasons embed into the occurrence-aware control certificate. -/
theorem toControl {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type code depth) :
    ControlExpressions.Tree source scope (fun _ => reason) id type code depth := by
  induction tree with
  | unit metadata form => exact .unit metadata form
  | bool value metadata form => exact .bool value metadata form
  | word value metadata form meaning => exact .word value metadata form meaning
  | localRead metadata form owned slot => exact .localRead metadata form owned slot
  | group metadata form _ child => exact .group metadata form child
  | pair metadata form _ _ left right => exact .pair metadata form left right

theorem readOnly {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type code depth) : Core.ReadOnly.Expression code :=
  Control.readOnly (toControl tree)

theorem preserves {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reason : Core.Word}
    {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope reason id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment heap (fun _ => reason)
        id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store :=
  Control.preserves (toControl tree) program context evidence environments heaps

theorem lowerExpression_preserves {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment heap (fun _ => reason)
        id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact preserves tree program context evidence environments heaps

end Basic

end Solcore.SourceSemantics.CoreLowering.GeneralExpressions
