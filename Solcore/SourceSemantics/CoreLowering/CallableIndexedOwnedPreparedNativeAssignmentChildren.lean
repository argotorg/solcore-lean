import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates

/-! The actual compatible assignment supplies raw child typing from its one
Core typing receipt. The three RHS insertions and one packed-key insertion
are removed syntactically. The real ordered key generation then supplies each
static child factory with that same local witness, including repeated keys.
No Source authority or expression execution is inferred. The present RHS
leaf follows from the actual modifier and setter annotations.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates
open TypedLexicalWhile.Native

/-- This is the actual arbitrary result selected by native constructor
inversion. Authentic compiler shape may normalize it at a separate leaf. -/
abbrev RawTyped (context : Core.Context) (expression : Expr) (definitions : DataEnvironment) : Prop :=
  ∃ result, HasType context expression result definitions

/-- The compiler's packed expression retains every original raw key witness
in its original order. Its product annotations are not used to infer any
Source node or Source type. -/
theorem packed_children {codes : List SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context (SourceCoreCalls.packArguments codes).expression result definitions) :
    ∀ code, code ∈ codes → RawTyped context code.expression definitions := by
  induction codes generalizing context result with
  | nil =>
      intro code member
      cases member
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [SourceCoreCalls.packArguments] at typed
          intro code member
          have same : code = head := by simpa only [List.mem_singleton] using member
          subst code
          exact ⟨_, typed⟩
      | cons next rest =>
          change HasType context
            (LocalSequence.pair head.type (SourceCoreCalls.packArguments (next :: rest)).type
              head.expression (SourceCoreCalls.packArguments (next :: rest)).expression)
            result definitions at typed
          cases typed with
          | caseE first failure remaining =>
              cases remaining with
              | caseE second failure returned =>
                  have remainingTyped := ih (remove_front second)
                  intro code member
                  rcases List.mem_cons.mp member with same | inTail
                  · subst code
                    exact ⟨_, first⟩
                  · exact remainingTyped code inTail

/-- Both raw compiler insertions are obtained from the same literal execute
code. This also applies to the real bitNot branch: the raw RHS may have an
arbitrary result there, so no declared leaf type is asserted. -/
theorem execute_children {prepared : Prepared} {reference rhs next : Expr}
    {keys : SourceCoreBasic.LoweredExpr} {output result : Ty}
    {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {definitions : DataEnvironment} {context : Core.Context}
    (typed : HasType context
      (execute prepared reference keys rhs next output operator bitNot invalid) result definitions) :
    RawTyped context rhs definitions ∧ RawTyped context keys.expression definitions := by
  cases typed with
  | letE reference first =>
      cases first with
      | caseE keysTyped failure second =>
          have rawKeys : RawTyped context keys.expression definitions := by
            simp only [shift, List.range, List.range.loop, List.foldl] at keysTyped
            exact ⟨_, remove_front keysTyped⟩
          cases second with
          | caseE snapshot failure third =>
              cases third with
              | caseE right failure fourth =>
                  have rawRight : RawTyped context rhs definitions := by
                    simp only [shift, List.range, List.range.loop, List.foldl] at right
                    exact ⟨_, remove_front (remove_front (remove_front right))⟩
                  exact ⟨rawRight, rawKeys⟩

private theorem modifier_slot {definitions : DataEnvironment} {context : Core.Context}
    {leaf payload failure : Ty} {operator : Option BinaryOp} {snapshot : Expr} {invalid : Word}
    (ordinary : ∀ op, operator = some op → op.rightType = op.resultType)
    (typed : HasType (payload :: context)
      (modified leaf operator false snapshot (.var 0) invalid) (.sum failure leaf) definitions) :
    payload = leaf := by
  cases operator with
  | none =>
      change HasType (payload :: context) (.inRight .word (.var 0)) (.sum failure leaf) definitions at typed
      cases typed with
      | inRight annotation value =>
          cases value with
          | var found =>
              simpa only [List.getElem?_cons_zero, Option.some.injEq] using found
  | some op =>
      simp only [modified, Bool.false_eq_true, ↓reduceIte, shift, List.range,
        List.range.loop, List.foldl, Expr.weakenAt, Nat.zero_le] at typed
      cases typed with
      | caseE selectedValue failed returned =>
          cases returned with
          | inRight annotation value =>
              cases value with
              | binary left right =>
                  cases right with
                  | var found =>
                      have slot : payload = op.rightType := by
                        simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                          Option.some.injEq] using found
                      exact slot.trans (ordinary op rfl)

private theorem assignment_operator_types (integer : Bool) (operator : Syntax.ValueAssignOp)
    {op : BinaryOp} (selected : binaryOperator integer operator = some op) :
    op.rightType = op.resultType := by
  cases integer <;> cases operator <;> simp only [binaryOperator, ↓reduceIte] at selected
  all_goals cases selected
  all_goals rfl

/-- A real present RHS is used by the modifier. The setter's literal
replacement annotation fixes its payload type; every actual compound
assignment operator has the same right operand and result type. The original
RHS failure binder fixes Word independently. No RHS typing is supplied. -/
theorem execute_present_rhs {prepared : Prepared} {reference rhs next : Expr}
    {keys : SourceCoreBasic.LoweredExpr} {output result : Ty}
    {operator : Syntax.ValueAssignOp} {invalid : Word}
    {definitions : DataEnvironment} {context : Core.Context}
    (typed : HasType context
      (execute prepared reference keys rhs next output
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result definitions) :
    HasType context rhs (LanguageResult.resultType prepared.route.leafType) definitions := by
  unfold execute LanguageResult.bind at typed
  cases typed with
  | letE reference first =>
      cases first with
      | caseE keysTyped keysFailure second =>
          cases second with
          | caseE selection selectionFailure third =>
              cases selection with
              | apply getterTyped argument =>
                  cases getterTyped with
                  | lambda parameterWF resultWF body =>
                      cases selectionFailure with
                      | inLeft outputWF reason =>
                          cases reason with
                          | var selectedAt =>
                              simp only [List.getElem?_cons_zero, Option.some.injEq] at selectedAt
                              subst_vars
                              cases third with
                              | caseE right rightFailure fourth =>
                                  cases rightFailure with
                                  | inLeft outputWF reason =>
                                      cases reason with
                                      | var failedAt =>
                                          simp only [List.getElem?_cons_zero, Option.some.injEq] at failedAt
                                          subst_vars
                                          cases fourth with
                                          | caseE modifiedTyped modifierFailure fifth =>
                                              cases fifth with
                                              | caseE written writeFailure last =>
                                                  cases written with
                                                  | apply setterTyped argument =>
                                                      cases setterTyped with
                                                      | lambda parameterWF resultWF body =>
                                                          cases argument with
                                                          | pair referenceTyped remaining =>
                                                              cases remaining with
                                                              | pair packedTyped replacement =>
                                                                  cases replacement with
                                                                  | var replacedAt =>
                                                                      simp only [List.getElem?_cons_zero,
                                                                        Option.some.injEq] at replacedAt
                                                                      subst_vars
                                                                      have same := modifier_slot
                                                                        (fun op accepted => assignment_operator_types _ _ accepted)
                                                                        modifiedTyped
                                                                      subst_vars
                                                                      apply remove_front
                                                                      apply remove_front
                                                                      apply remove_front
                                                                      simpa only [shift, List.range,
                                                                        List.range.loop, List.foldl,
                                                                        LanguageResult.resultType] using right

/-- Actual ordered keys feed their local native witnesses to the static
certificate factory. The factory is requested only for these same compiler
outputs. Repeated IDs and code entries keep repeated receipts. -/
theorem keys_of_generated {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {expression : ExpressionLowerer} {fuel : Nat} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {administrative : Core.Context} {definitions : DataEnvironment} {result : Ty}
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes)
    (native : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (SourceCoreCalls.packArguments codes).expression result definitions)
    (extract : ∀ id code, id ∈ DataPlaceKeyOrder.sourceKeys projections →
      expression fuel source scope id reasonAt = .ok code →
      RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) code.expression definitions →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes ∧
      keys.map Prod.snd = codes.map (·.type) := by
  have collect : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
      (∀ code, code ∈ codes → RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) code.expression definitions) →
      (∀ id code, id ∈ keys.map Prod.fst → expression fuel source scope id reasonAt = .ok code →
        RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) code.expression definitions →
        ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => intro _ _; exact ⟨.nil, rfl⟩
    | cons head tail ih =>
        intro known extract
        have rest := ih
          (fun code member => known code (List.mem_cons_of_mem _ member))
          (fun id code member accepted raw => extract id code (List.mem_cons_of_mem _ member) accepted raw)
        exact ⟨.cons (extract _ _ (by simp) head.1 (known _ (by simp))) rest.1,
          by simp only [List.map_cons, head.2, rest.2]⟩
  have receipts := collect generated (packed_children native)
    (fun id code member accepted raw => extract id code
      (by simpa only [PreparedPath.key_ids path] using member) accepted raw)
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [PreparedPath.key_ids path] at tree
  exact ⟨types, tree, receipts.2⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
