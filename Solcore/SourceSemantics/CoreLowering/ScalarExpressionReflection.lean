import Solcore.SourceSemantics.CoreLowering.GeneralExpressions

/-! Reflection of independently supplied source expression derivations for the
scalar/product compiler profile. This does not assume whole-language source
determinism. Administrative closure cells in the represented Core heap are
permitted and remain unchanged. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection

open Frontend Frontend.SourceInference TypeSystem LocalCell

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
    (ordinary : ∀ name binder location cell,
      node.form = .reference name (.local binder) →
      Dynamic.Environment.LooksUp environment binder location →
      Dynamic.Heap.Reads before location cell → cell.generalized = none)
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
  | generalizedLocal otherContains form _ lookup read descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      rw [same] at form
      have absent := ordinary _ _ _ _ form lookup read
      rw [absent] at descriptor
      cases descriptor

private theorem word_constructs {span : Syntax.SourceSpan}
    {literal : Syntax.CoreLiteralValue} {value : Core.Word}
    (meaning : WordLiteralDenotes ⟨span, literal⟩ value) :
    Dynamic.LiteralConstructs literal (.word value) := by
  have modulo : Core.Word.ofNatModulo value.val = value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  rw [← modulo]
  exact .word meaning

namespace Control

open ControlExpressions

/-- Every successful independent source derivation for this structural tree
has the compiled value and an unchanged heap. No source evaluation premise is
hidden in the tree, and no first-order restriction is imposed on other cells. -/
theorem source_success
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {value : Dynamic.Value}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment heap id value after) :
    after = heap ∧ ∃ staged : SourceStagedValue.Value,
      value = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = type ∧
      Core.Evaluates coreEnvironment store code (.inRight .word (SourceStagedValue.toCore staged)) store := by
  induction tree generalizing value after with
  | unit metadata form =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements
          cases pack
          exact ⟨rfl, .unit, rfl, rfl, .inRight .unit⟩
  | bool boolean metadata form =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw
      exact ⟨rfl, .bool boolean, rfl, rfl, .inRight .bool⟩
  | word word metadata form meaning =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | literal _ construction =>
          exact ⟨rfl, .word word, Dynamic.LiteralConstructs.functional construction
            (word_constructs meaning), rfl, .inRight .word⟩
  | @localRead id node type binder name index metadata form _ slot =>
      obtain ⟨location, target, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have ordinary : ∀ otherName otherBinder otherLocation otherCell,
          node.form = .reference otherName (.local otherBinder) →
          Dynamic.Environment.LooksUp environment otherBinder otherLocation →
          Dynamic.Heap.Reads heap otherLocation otherCell → otherCell.generalized = none := by
        intro otherName otherBinder otherLocation otherCell sameForm otherLookup otherRead
        rw [form] at sameForm
        cases sameForm
        have sameLocation := Dynamic.Environment.LooksUp.functional lookup otherLookup
        subst otherLocation
        have sameCell := Dynamic.Heap.Reads.functional read otherRead
        subst otherCell
        cases related <;> rfl
      have raw := expression_evaluation_raw unique metadata.contains ordinary metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | «local» _ otherLookup otherRead _ initialized =>
          have sameLocation := Dynamic.Environment.LooksUp.functional lookup otherLookup
          subst_vars
          have sameCell := Dynamic.Heap.Reads.functional read otherRead
          subst_vars
          cases related with
          | uninitialized => cases initialized
          | initialized staged =>
              cases initialized
              exact ⟨rfl, staged, rfl, rfl,
                Core.OptionalCell.read_success (reasonAt id) (.var coreLookup) coreRead⟩
      | localEmptyMapping _ otherLookup otherRead _ mappingType _ _ =>
          have sameLocation := Dynamic.Environment.LooksUp.functional lookup otherLookup
          subst_vars
          have sameCell := Dynamic.Heap.Reads.functional read otherRead
          subst_vars
          exact False.elim (related.types.not_mapping ⟨_, _, mappingType⟩)
  | group metadata form _ ih =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | group _ child => exact ih child
  | pair metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  obtain ⟨rfl, leftValue, rfl, leftType, leftCore⟩ := leftIH left
                  obtain ⟨rfl, rightValue, rfl, rightType, rightCore⟩ := rightIH right
                  refine ⟨rfl, .product leftValue rightValue,
                    Dynamic.ValuesPack.functional pack (.cons (.singleton _)), ?_, ?_⟩
                  · simp [SourceStagedValue.coreType, leftType, rightType]
                  · exact Core.LocalSequence.pair_success _ _ leftCore
                      ((GeneralExpressions.Control.readOnly rightTree).evaluation_weakenAt_zero rightCore _)
  | conditional metadata form conditionTree thenTree elseTree conditionIH thenIH elseIH =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | conditionalTrue _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := conditionIH condition
          obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
          cases same
          obtain ⟨rfl, result, rfl, resultType, branchCore⟩ := thenIH branch
          exact ⟨rfl, result, rfl, resultType, Core.LocalControl.choose_true _ conditionCore
            ((GeneralExpressions.Control.readOnly thenTree).evaluation_weakenAt_zero branchCore _)⟩
      | conditionalFalse _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := conditionIH condition
          obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
          cases same
          obtain ⟨rfl, result, rfl, resultType, branchCore⟩ := elseIH branch
          exact ⟨rfl, result, rfl, resultType, Core.LocalControl.choose_false _ conditionCore
            ((GeneralExpressions.Control.readOnly elseTree).evaluation_weakenAt_zero branchCore _)⟩

end Control

private theorem expression_fault_raw
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node)
    (ordinary : ∀ name binder location cell,
      node.form = .reference name (.local binder) →
      Dynamic.Environment.LooksUp environment binder location →
      Dynamic.Heap.Reads before location cell → cell.generalized = none)
    (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment
      before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form otherContains form =>
      exact contains_unique unique otherContains contains ▸ form
  | coercion otherContains _ fault =>
      have same := contains_unique unique otherContains contains
      rw [same, empty] at fault
      cases fault
  | generalizedLocalRequirement otherContains form _ lookup read descriptor _ _ _
  | generalizedLocalCoercion otherContains form _ lookup read descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      rw [same] at form
      have absent := ordinary _ _ _ _ form lookup read
      rw [absent] at descriptor
      cases descriptor

namespace Control

open ControlExpressions

/-- Within the scalar tree, every independently specified expression fault
is an absent ordinary local read on the executed path. -/
theorem source_fault
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : Dynamic.ExpressionFaults program context evidence source environment heap id reason after) :
    after = heap ∧ ∃ site location,
      reason = .uninitializedLocation location ∧
      UninitializedAt program context evidence source environment heap id site location ∧
      Core.Evaluates coreEnvironment store code (.inLeft type (.word (reasonAt site))) store := by
  induction tree generalizing reason after with
  | unit metadata form =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | tuple _ elements => cases elements
  | bool _ metadata form | word _ metadata form _ =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw
  | @localRead id node type binder name index metadata form owned slot =>
      obtain ⟨location, target, cell, stored, lookup, coreLookup, _, read, coreRead, related⟩ :=
        environments.lookup_heap heaps slot
      have ordinary : ∀ otherName otherBinder otherLocation otherCell,
          node.form = .reference otherName (.local otherBinder) →
          Dynamic.Environment.LooksUp environment otherBinder otherLocation →
          Dynamic.Heap.Reads heap otherLocation otherCell → otherCell.generalized = none := by
        intro otherName otherBinder otherLocation otherCell sameForm otherLookup otherRead
        rw [form] at sameForm
        cases sameForm
        have sameLocation := Dynamic.Environment.LooksUp.functional lookup otherLookup
        subst otherLocation
        have sameCell := Dynamic.Heap.Reads.functional read otherRead
        subst otherCell
        cases related <;> rfl
      have raw := expression_fault_raw unique metadata.contains ordinary metadata.coercions fault
      rw [form] at raw
      cases raw with
      | localUnbound _ unbound => exact False.elim (unbound.excludes_lookup lookup)
      | localDangling _ otherLookup dangling =>
          have same := Dynamic.Environment.LooksUp.functional lookup otherLookup
          subst_vars
          exact False.elim (dangling.excludes_read read)
      | localUninitialized _ otherLookup otherRead _ empty _ =>
          have sameLocation := Dynamic.Environment.LooksUp.functional lookup otherLookup
          subst_vars
          have sameCell := Dynamic.Heap.Reads.functional read otherRead
          subst_vars
          have cellType := related.types.source_unique metadata.types
          let site : ReadSite source scope id type := {
            node, binder, name, index, contains := metadata.contains, form, owner := owned
            requirements := metadata.requirements, coercions := metadata.coercions
            slot, types := metadata.types
          }
          cases related with
          | uninitialized types =>
              exact ⟨rfl, id, _, rfl, .localRead site lookup read cellType rfl rfl,
                Core.OptionalCell.read_failure (reasonAt id) (.var coreLookup) coreRead⟩
          | initialized staged => cases empty
  | group metadata form _ ih =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | group _ child =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := ih child
          exact ⟨rfl, site, location, rfl, .group metadata form origin, core⟩
  | pair metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | tuple _ elements =>
          cases elements with
          | head left =>
              obtain ⟨rfl, site, location, rfl, origin, core⟩ := leftIH left
              exact ⟨rfl, site, location, rfl, .pairLeft metadata form origin,
                Core.LocalSequence.pair_left_failure _ _ core⟩
          | tail left rest =>
              obtain ⟨rfl, staged, same, _, core⟩ := source_success leftTree unique environments heaps left
              cases rest with
              | head right =>
                  obtain ⟨rfl, site, location, rfl, origin, rightCore⟩ := rightIH right
                  exact ⟨rfl, site, location, rfl, .pairRight metadata form left origin,
                    Core.LocalSequence.pair_right_failure _ _ core
                      ((GeneralExpressions.Control.readOnly rightTree).evaluation_weakenAt_zero rightCore _)⟩
              | tail _ impossible => cases impossible
  | conditional metadata form conditionTree thenTree elseTree conditionIH thenIH elseIH =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | conditionalCondition _ child =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := conditionIH child
          exact ⟨rfl, site, location, rfl, .condition metadata form origin,
            Core.LocalControl.choose_failure _ core⟩
      | conditionalType _ condition notBool _ =>
          obtain ⟨_, staged, rfl, typed, _⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
          exact False.elim (notBool trivial)
      | conditionalTrueBranch _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
          cases same
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := thenIH branch
          exact ⟨rfl, site, location, rfl, .thenBranch metadata form condition origin,
            Core.LocalControl.choose_true _ conditionCore
              ((GeneralExpressions.Control.readOnly thenTree).evaluation_weakenAt_zero core _)⟩
      | conditionalFalseBranch _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
          cases same
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := elseIH branch
          exact ⟨rfl, site, location, rfl, .elseBranch metadata form condition origin,
            Core.LocalControl.choose_false _ conditionCore
              ((GeneralExpressions.Control.readOnly elseTree).evaluation_weakenAt_zero core _)⟩

end Control

namespace Primitive

open PrimitiveExpressions

private theorem no_owned {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout [] [] owned) : owned = [] := by
  simpa [Dynamic.OrdinaryRequirementLayout, coercionRequirementIds] using layout.symm

private theorem unary_primitive
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {operator : Syntax.UnaryOp} {input output : Dynamic.Value}
    (applied : Dynamic.UnaryOperationApplies program context evidence before operator [] input output after) :
    after = before ∧ Dynamic.UnaryPrimitiveApplies operator input output := by
  cases applied with
  | primitive applies => exact ⟨rfl, applies⟩
  | method _ selected _ => cases selected

private theorem binary_primitive
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {operator : Syntax.BinaryOp} {left right output : Dynamic.Value}
    (applied : Dynamic.BinaryOperationApplies program context evidence before operator [] left right output after) :
    after = before ∧ Dynamic.BinaryPrimitiveApplies operator left right output := by
  cases applied with
  | primitive applies => exact ⟨rfl, applies⟩
  | method _ selected _ => cases selected

/-- Successful independent scalar primitive evaluations have exactly the
compiled result. The retained evidence needed to construct a source execution
is not assumed here: a supplied successful integer-literal derivation already
contains that evidence. -/
theorem source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {value : Dynamic.Value}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment heap id value after) :
    after = heap ∧ ∃ staged : SourceStagedValue.Value,
      value = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = type ∧
      Core.Evaluates coreEnvironment store code (.inRight .word (SourceStagedValue.toCore staged)) store := by
  induction tree generalizing value after with
  | control tree => exact Control.source_success tree unique environments heaps evaluated
  | integerLiteral metadata form =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | integerLiteral _ construction =>
          cases construction with
          | word => exact ⟨rfl, .word _, rfl, rfl, .inRight .word⟩
          | integer => cases metadata.target
  | unary operator metadata form child ih =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form, metadata.requirements, metadata.coercions] at raw
      cases raw with
      | unary layout childEvaluation applied =>
          have ownedEmpty := no_owned layout
          subst_vars
          obtain ⟨rfl, staged, rfl, typed, core⟩ := ih childEvaluation
          obtain ⟨rfl, primitiveApplied⟩ := unary_primitive applied
          obtain ⟨result, resultTyped, sourceApplied, coreApplied⟩ := unary_value operator staged typed
          exact ⟨rfl, result, Dynamic.UnaryPrimitiveApplies.functional primitiveApplied sourceApplied,
            resultTyped, Core.LocalPrimitiveResults.unary_success core coreApplied⟩
  | binary operator metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form, metadata.requirements, metadata.coercions] at raw
      cases raw with
      | binaryShortCircuit _ leftEvaluation circuit _ =>
          obtain ⟨rfl, staged, same, typed, core⟩ := leftIH leftEvaluation
          cases circuit with
          | andFalse =>
              obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
              cases same
              exact ⟨rfl, .bool false, rfl, rfl, Core.LocalPrimitiveResults.logicalAnd_shortCircuit core⟩
          | orTrue =>
              obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
              cases same
              exact ⟨rfl, .bool true, rfl, rfl, Core.LocalPrimitiveResults.logicalOr_shortCircuit core⟩
      | binaryEvaluateRight layout leftEvaluation evaluateRight rightEvaluation applied =>
          have ownedEmpty := no_owned layout
          subst_vars
          obtain ⟨rfl, leftValue, rfl, leftTyped, leftCore⟩ := leftIH leftEvaluation
          obtain ⟨rfl, rightValue, rfl, rightTyped, rightCore⟩ := rightIH rightEvaluation
          obtain ⟨rfl, primitiveApplied⟩ := binary_primitive applied
          have shifted := (GeneralExpressions.Primitive.readOnly rightTree).evaluation_weakenAt_zero rightCore
            (SourceStagedValue.toCore leftValue)
          by_cases strict : Dynamic.StrictBinaryOperator operator
          · obtain ⟨leftWord, rfl⟩ := word_of_type leftValue (leftTyped.trans (strict_operand_word strict))
            obtain ⟨rightWord, rfl⟩ := word_of_type rightValue (rightTyped.trans (strict_operand_word strict))
            obtain ⟨result, resultTyped, sourceApplied, bodyEvaluation⟩ := strict_binary_value strict leftWord rightWord
            refine ⟨rfl, result, Dynamic.BinaryPrimitiveApplies.functional primitiveApplied sourceApplied, resultTyped, ?_⟩
            rw [binary_strict strict]
            exact Core.LocalPrimitiveResults.binaryWith_success leftCore shifted (bodyEvaluation _ _)
          · rcases binary_nonstrict strict with isAnd | isOr
            · subst operator
              obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
              cases evaluateRight with
              | strict impossible => cases impossible
              | andTrue =>
                  exact ⟨rfl, .bool rightBoolean,
                    Dynamic.BinaryPrimitiveApplies.functional primitiveApplied (.logicalAnd true rightBoolean),
                    rfl, Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
            · subst operator
              obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
              cases evaluateRight with
              | strict impossible => cases impossible
              | orFalse =>
                  exact ⟨rfl, .bool rightBoolean,
                    Dynamic.BinaryPrimitiveApplies.functional primitiveApplied (.logicalOr false rightBoolean),
                    rfl, Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
  | group metadata form _ ih =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | group _ child => exact ih child
  | pair metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | tuple _ elements pack =>
          cases elements with
          | cons left rest =>
              cases rest with
              | cons right rest =>
                  cases rest
                  obtain ⟨rfl, leftValue, rfl, leftType, leftCore⟩ := leftIH left
                  obtain ⟨rfl, rightValue, rfl, rightType, rightCore⟩ := rightIH right
                  refine ⟨rfl, .product leftValue rightValue,
                    Dynamic.ValuesPack.functional pack (.cons (.singleton _)), ?_, ?_⟩
                  · simp [SourceStagedValue.coreType, leftType, rightType]
                  · exact Core.LocalSequence.pair_success _ _ leftCore
                      ((GeneralExpressions.Primitive.readOnly rightTree).evaluation_weakenAt_zero rightCore _)
  | conditional metadata form conditionTree thenTree elseTree conditionIH thenIH elseIH =>
      have raw := expression_evaluation_raw unique metadata.contains
        (by simp [form]) metadata.coercions evaluated
      rw [form] at raw
      cases raw with
      | conditionalTrue _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := conditionIH condition
          obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
          cases same
          obtain ⟨rfl, result, rfl, resultType, branchCore⟩ := thenIH branch
          exact ⟨rfl, result, rfl, resultType, Core.LocalControl.choose_true _ conditionCore
            ((GeneralExpressions.Primitive.readOnly thenTree).evaluation_weakenAt_zero branchCore _)⟩
      | conditionalFalse _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := conditionIH condition
          obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
          cases same
          obtain ⟨rfl, result, rfl, resultType, branchCore⟩ := elseIH branch
          exact ⟨rfl, result, rfl, resultType, Core.LocalControl.choose_false _ conditionCore
            ((GeneralExpressions.Primitive.readOnly elseTree).evaluation_weakenAt_zero branchCore _)⟩

private theorem unary_fault_excluded
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {operator : Syntax.UnaryOp} {input output : Dynamic.Value}
    {reason : Dynamic.SemanticFault}
    (applied : Dynamic.UnaryPrimitiveApplies operator input output)
    (fault : Dynamic.UnaryOperationFaults program context evidence before operator [] input reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | requirement fault => cases fault
  | method _ selected _ => cases selected

private theorem binary_fault_excluded
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {operator : Syntax.BinaryOp} {left right output : Dynamic.Value}
    {reason : Dynamic.SemanticFault}
    (applied : Dynamic.BinaryPrimitiveApplies operator left right output)
    (fault : Dynamic.BinaryOperationFaults program context evidence before operator [] left right reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | requirement fault => cases fault
  | method _ selected _ => cases selected

private theorem typed_binary_applies (operator : Syntax.BinaryOp) (left right : SourceStagedValue.Value)
    (leftTyped : SourceStagedValue.coreType left = SourceCorePrimitive.binaryOperandType operator)
    (rightTyped : SourceStagedValue.coreType right = SourceCorePrimitive.binaryOperandType operator) :
    ∃ output, Dynamic.BinaryPrimitiveApplies operator (StagedValue.toSource left) (StagedValue.toSource right) output := by
  by_cases strict : Dynamic.StrictBinaryOperator operator
  · obtain ⟨leftWord, rfl⟩ := word_of_type left (leftTyped.trans (strict_operand_word strict))
    obtain ⟨rightWord, rfl⟩ := word_of_type right (rightTyped.trans (strict_operand_word strict))
    obtain ⟨result, _, applied, _⟩ := strict_binary_value strict leftWord rightWord
    exact ⟨_, applied⟩
  · rcases binary_nonstrict strict with isAnd | isOr <;> subst operator
    · obtain ⟨leftBoolean, rfl⟩ := bool_of_type left leftTyped
      obtain ⟨rightBoolean, rfl⟩ := bool_of_type right rightTyped
      exact ⟨_, .logicalAnd leftBoolean rightBoolean⟩
    · obtain ⟨leftBoolean, rfl⟩ := bool_of_type left leftTyped
      obtain ⟨rightBoolean, rfl⟩ := bool_of_type right rightTyped
      exact ⟨_, .logicalOr leftBoolean rightBoolean⟩

/-- Retained literal evidence needs a covering runtime dictionary to rule out
an independently specified evidence-closure fault. Under that explicit entry
condition, scalar primitive faults are precisely propagated absent reads. -/
theorem source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : Dynamic.ExpressionFaults program context evidence source environment heap id reason after) :
    after = heap ∧ ∃ site location,
      reason = .uninitializedLocation location ∧
      UninitializedAt program context evidence source environment heap id site location ∧
      Core.Evaluates coreEnvironment store code (.inLeft type (.word (reasonAt site))) store := by
  induction tree generalizing reason after with
  | control tree =>
      obtain ⟨rfl, site, location, rfl, origin, core⟩ := Control.source_fault tree unique environments heaps fault
      exact ⟨rfl, site, location, rfl, .control origin, core⟩
  | @integerLiteral id node literal resolution metadata form =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | integerRequirement _ unavailable =>
          have proves : RequirementProves context resolution.requirement (ProgramSignatures.builtinIntPredicate .word) := by
            obtain ⟨solved, member, identifier, predicate⟩ := metadata.requirement
            have contains : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
            exact ⟨solved, ⟨contains, identifier⟩, predicate, valid.valid.entriesValid solved contains⟩
          obtain ⟨closed, produced⟩ := Dynamic.RequirementProves.produces_of_covers covers proves
          exact False.elim (produced.excludes_unavailable valid.valid.idsUnique unavailable)
  | unary operator metadata form child ih =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form, metadata.requirements, metadata.coercions] at raw
      cases raw with
      | unaryOperand _ childFault =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := ih childFault
          exact ⟨rfl, site, location, rfl, .unary metadata form origin,
            Core.LocalPrimitiveResults.unary_failure core⟩
      | unaryApply layout childEvaluation operationFault =>
          have ownedEmpty := no_owned layout
          subst_vars
          obtain ⟨rfl, staged, rfl, typed, _⟩ := source_success child unique environments heaps childEvaluation
          obtain ⟨result, _, applied, _⟩ := unary_value operator staged typed
          exact False.elim (unary_fault_excluded applied operationFault)
  | binary operator metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form, metadata.requirements, metadata.coercions] at raw
      cases raw with
      | binaryLeft _ childFault =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := leftIH childFault
          exact ⟨rfl, site, location, rfl, .binaryLeft metadata form origin, binary_left_failure core⟩
      | binaryLeftOperand _ leftEvaluation invalid =>
          obtain ⟨_, staged, rfl, typed, _⟩ := source_success leftTree unique environments heaps leftEvaluation
          cases invalid with
          | logicalAnd notBool | logicalOr notBool =>
              obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
              exact False.elim (notBool trivial)
      | binaryRight _ leftEvaluation evaluateRight rightFault =>
          obtain ⟨rfl, staged, same, typed, leftCore⟩ := source_success leftTree unique environments heaps leftEvaluation
          obtain ⟨rfl, site, location, rfl, origin, rightCore⟩ := rightIH rightFault
          refine ⟨rfl, site, location, rfl, .binaryRight metadata form leftEvaluation evaluateRight origin, ?_⟩
          have shifted := (GeneralExpressions.Primitive.readOnly rightTree).evaluation_weakenAt_zero rightCore
            (SourceStagedValue.toCore staged)
          cases evaluateRight with
          | strict strict =>
              rw [binary_strict strict]
              exact Core.LocalPrimitiveResults.binaryWith_right_failure leftCore shifted
          | andTrue =>
              obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
              cases same
              exact Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted
          | orFalse =>
              obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
              cases same
              exact Core.LocalPrimitiveResults.logicalOr_right leftCore shifted
      | binaryApply layout leftEvaluation _ rightEvaluation operationFault =>
          have ownedEmpty := no_owned layout
          subst_vars
          obtain ⟨rfl, left, rfl, leftTyped, _⟩ := source_success leftTree unique environments heaps leftEvaluation
          obtain ⟨rfl, right, rfl, rightTyped, _⟩ := source_success rightTree unique environments heaps rightEvaluation
          obtain ⟨output, applied⟩ := typed_binary_applies operator left right leftTyped rightTyped
          exact False.elim (binary_fault_excluded applied operationFault)
  | group metadata form _ ih =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | group _ child =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := ih child
          exact ⟨rfl, site, location, rfl, .group metadata form origin, core⟩
  | pair metadata form leftTree rightTree leftIH rightIH =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | tuple _ elements =>
          cases elements with
          | head left =>
              obtain ⟨rfl, site, location, rfl, origin, core⟩ := leftIH left
              exact ⟨rfl, site, location, rfl, .pairLeft metadata form origin,
                Core.LocalSequence.pair_left_failure _ _ core⟩
          | tail left rest =>
              obtain ⟨rfl, staged, same, _, core⟩ := source_success leftTree unique environments heaps left
              cases rest with
              | head right =>
                  obtain ⟨rfl, site, location, rfl, origin, rightCore⟩ := rightIH right
                  exact ⟨rfl, site, location, rfl, .pairRight metadata form left origin,
                    Core.LocalSequence.pair_right_failure _ _ core
                      ((GeneralExpressions.Primitive.readOnly rightTree).evaluation_weakenAt_zero rightCore _)⟩
              | tail _ impossible => cases impossible
  | conditional metadata form conditionTree thenTree elseTree conditionIH thenIH elseIH =>
      have raw := expression_fault_raw unique metadata.contains (by simp [form]) metadata.coercions fault
      rw [form] at raw
      cases raw with
      | conditionalCondition _ child =>
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := conditionIH child
          exact ⟨rfl, site, location, rfl, .condition metadata form origin,
            Core.LocalControl.choose_failure _ core⟩
      | conditionalType _ condition notBool _ =>
          obtain ⟨_, staged, rfl, typed, _⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
          exact False.elim (notBool trivial)
      | conditionalTrueBranch _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
          cases same
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := thenIH branch
          exact ⟨rfl, site, location, rfl, .thenBranch metadata form condition origin,
            Core.LocalControl.choose_true _ conditionCore
              ((GeneralExpressions.Primitive.readOnly thenTree).evaluation_weakenAt_zero core _)⟩
      | conditionalFalseBranch _ condition branch =>
          obtain ⟨rfl, staged, same, typed, conditionCore⟩ := source_success conditionTree unique environments heaps condition
          obtain ⟨boolean, rfl⟩ := bool_of_type staged typed
          cases same
          obtain ⟨rfl, site, location, rfl, origin, core⟩ := elseIH branch
          exact ⟨rfl, site, location, rfl, .elseBranch metadata form condition origin,
            Core.LocalControl.choose_false _ conditionCore
              ((GeneralExpressions.Primitive.readOnly elseTree).evaluation_weakenAt_zero core _)⟩

/-- Relate the particular source outcome supplied by the caller, rather than
only constructing some independent source execution. -/
theorem source_outcome
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (evaluated : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    after = heap ∧ ∃ result,
      OutcomeRepresents program context evidence source environment heap reasonAt id type outcome result ∧
      Core.Evaluates coreEnvironment store code result store := by
  cases evaluated with
  | value evaluated =>
      obtain ⟨rfl, staged, rfl, typed, core⟩ := source_success tree unique environments heaps evaluated
      exact ⟨rfl, _, .value staged typed, core⟩
  | fault fault =>
      obtain ⟨rfl, site, location, rfl, origin, core⟩ := source_fault tree unique valid covers environments heaps fault
      exact ⟨rfl, _, .uninitialized site location origin, core⟩

/-- The same result survives an administrative environment insertion or any
lookup-preserving renaming. Existing captured closures are not rewritten. -/
theorem source_outcome_rename
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {coreEnvironment actualEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context} {ξ : Core.Renaming}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ coreEnvironment actualEnvironment)
    (evaluated : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    after = heap ∧ ∃ result,
      OutcomeRepresents program context evidence source environment heap reasonAt id type outcome result ∧
      Core.Evaluates actualEnvironment store (code.rename ξ) result store := by
  obtain ⟨same, result, related, core⟩ := source_outcome tree unique valid covers environments heaps evaluated
  exact ⟨same, result, related, (GeneralExpressions.Primitive.readOnly tree).evaluation_rename core agree⟩

theorem source_success_functional
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap leftHeap rightHeap : Dynamic.Heap} {left right : Dynamic.Value}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (leftEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment heap id left leftHeap)
    (rightEvaluation : Dynamic.ExpressionEvaluates program context evidence source environment heap id right rightHeap) :
    left = right ∧ leftHeap = heap ∧ rightHeap = heap := by
  obtain ⟨rfl, leftStaged, rfl, _, leftCore⟩ := source_success tree unique environments heaps leftEvaluation
  obtain ⟨rfl, rightStaged, rfl, _, rightCore⟩ := source_success tree unique environments heaps rightEvaluation
  have same := (Core.evaluation_deterministic leftCore rightCore).1
  have stagedSame := SourceStagedValue.toCore_injective (Core.Value.inRight.inj same).2
  exact ⟨congrArg StagedValue.toSource stagedSame, rfl, rfl⟩

theorem source_success_excludes_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty}
    {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap valueHeap faultHeap : Dynamic.Heap}
    {value : Dynamic.Value} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment heap id value valueHeap)
    (fault : Dynamic.ExpressionFaults program context evidence source environment heap id reason faultHeap) : False := by
  obtain ⟨_, _, _, _, succeeded⟩ := source_success tree unique environments heaps evaluated
  obtain ⟨_, _, _, _, _, failed⟩ := source_fault tree unique valid covers environments heaps fault
  have impossible := (Core.evaluation_deterministic succeeded failed).1
  cases impossible

/-- Actual compiler acceptance and a particular finite independent source
execution imply a finite Core run. Every completed run agrees with that
execution; fuel exhaustion is not classified as a source result. -/
theorem lowerExpression_source_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (evaluated : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    after = heap ∧ ∃ result required,
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type outcome result ∧
      (∀ runtimeFuel, required ≤ runtimeFuel →
        Core.runStateful runtimeFuel (.initial lowered.expression coreEnvironment store) = .done result store) ∧
      (∀ runtimeFuel actual actualStore,
        Core.runStateful runtimeFuel (.initial lowered.expression coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = store) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  obtain ⟨same, result, related, core⟩ := source_outcome tree unique valid covers environments heaps evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel core
  exact ⟨same, result, required, related, completes, fun _ _ _ completed =>
    Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) core⟩

end Primitive

end Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection
