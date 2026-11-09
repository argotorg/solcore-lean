import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas

/-!
# Prepared callables: native collectors

Native collectors of assignments, `for` headers, imperative and branching statements, and joint bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
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
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
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
    {leaf payload failure : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {snapshot : Expr} {invalid : Word}
    (ordinary : ∀ op, operator = some op → op.operation.rightType = op.operation.resultType)
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
                      have slot : payload = op.operation.rightType := by
                        simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                          Option.some.injEq] using found
                      exact slot.trans (ordinary op rfl)

private theorem assignment_operator_types (integer : Bool) (operator : Syntax.ValueAssignOp)
    {op : Frontend.SourceCoreDataPlaces.Modifier} (selected : binaryOperator integer operator = some op) :
    op.operation.rightType = op.operation.resultType := by
  cases integer <;> cases operator <;>
    simp only [binaryOperator, Frontend.SourceCoreDataPlaces.Modifier.total, ↓reduceIte] at selected
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
/-! Actual compatible lowering and its enclosing native typing manufacture
all local RHS/key witnesses for the static expression factory. The original
Source typing, writable route, prepared layout, full node identity and exact
assignment token remain independent. No expected child typing or expression
execution is supplied by a callback. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates
open GenericAssignmentStatements CallableIndexedOwnedPreparedNativeAssignmentChildren

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

/-- The same real Head.PreparedAt is produced with the original layout.
The expression factory receives the actual raw Core witness at this Source
occurrence, from this lowering, scope, context and compiler fuel. -/
theorem Head.of_lower_with_raw_occurrences {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered →
      RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression definitions →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand ∧
        head.PreparedAt site fuel invalidProjection missing := by
  classical
  by_cases bare : assignment.target.projections = []
  · obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
    have rhsNative := execute_present_rhs (prepared := prepared) (reference := .var index)
      (keys := SourceCoreCalls.packArguments []) (rhs := value.expression) (next := next)
      (output := output) (result := result) (operator := operator) (codeEq ▸ typed)
    obtain ⟨head, emitted, token⟩ := Head.of_lower_bare_with_token bare unique writable rightTyped profile
      (fun lowered acceptedRight => by
        have same : lowered = value := Except.ok.inj (acceptedRight.symm.trans generated)
        subst lowered
        exact extract rhs value (by simp) generated ⟨_, rhsNative⟩) accepted
    exact ⟨head, emitted, token, .bare bare⟩
  · cases generated_of_lower accepted with
    | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
      cases rhsGenerated with
      | @present id right rhsGenerated rhsType =>
        obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
        obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
        have rhsNative := execute_present_rhs (prepared := prepared) (reference := .var index)
          (keys := SourceCoreCalls.packArguments codes) (rhs := right.expression) (next := next)
          (output := output) (result := result) (operator := operator)
          (by simpa only [routeEq, Option.isNone_some] using typed)
        obtain ⟨node, found, certified⟩ := extract rhs right (by simp) rhsGenerated ⟨_, rhsNative⟩
        obtain ⟨_rhsRaw, ⟨packedResult, packedNative⟩⟩ := execute_children typed
        obtain ⟨sourceTypes, tree, keyTypes⟩ :=
          CallableIndexedOwnedPreparedNativeAssignmentChildren.keys_of_generated path generated packedNative
            (fun id code member compiled raw => extract id code (List.mem_cons_of_mem rhs member) compiled raw)
        obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
        have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
        have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
            0 prepared.steps prepared.keys leaf := rootEq ▸ path
        have rhsType : right.type = prepared.route.leafType := by simpa only [routeEq] using rhsType.symm
        have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
            assignment.target prepared codes sourceTypes leaf administrative := by
          refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
            CompatiblePlaceHelperTyping.getter_of_execute typed,
            CompatiblePlaceHelperTyping.setter_of_execute typed (CompatiblePlaceHelperTyping.rhs_shift_typed (by simpa only [rhsType] using rhsNative))⟩
          · rw [← values.checked.catalog.project_runtimeType leaf, description.selectedType,
              values.checked.catalog.project_runtimeType, routeEq]
            exact description.leafProjected
          · intro k v declared
            rw [routeEq]
            exact description.virtual k v (rootEq.symm.trans declared)
          · intro empty
            have length := PreparedPath.steps_length path
            rw [empty, List.length_nil] at length
            exact bare (List.eq_nil_of_length_eq_zero length.symm)
        have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
          intro notMapping
          rw [routeEq]
          exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))
        have rawType := stored_type unique found rightTyped
        refine ⟨⟨prepared, index, codes, leaf, right, node, invalidOperand,
          .projected layout ordinary, by simpa only [routeEq] using lookup, rootEq ▸ writable binder description.binding,
          found, certified, by simpa only [rawType] using leafView, rhsType, ?_⟩, by simp [Head.emit, routeEq], rfl, ?_⟩
        · rcases profile with equal | word | ⟨integer, notWordOnly⟩
          · exact .inl equal
          · exact .inr (.inl (leafView.trans word))
          · exact .inr (.inr ⟨leafView.trans integer, notWordOnly⟩)
        · exact .projected route layout ordinary rfl described preparedBy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors
/-! Actual for-item syntax/compiler induction adds the native witness of each
initializer/discard occurrence from its literal outer bind. The continuation,
marked allocation, original Source typing and diagnostic origin stay exact.
Actual assignment RHS/keys derive their own native witnesses from this same
code. No expected child typing or body execution law is accepted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors
open Core Frontend SourceInference GenericForHeader
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)

private theorem unary_ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Native typing is manufactured at the actual initialized/discard child.
Assignment factories remain separate until their original wrappers are inverted. -/
theorem extraction_of_lowerForItems_with_coupled (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates sourceContext scope id lowered)

    {next : Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = residualMode →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm}
    (syntaxTree : Syntax source expressionSyntax context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor tracked source parentSite items) :
    Nonempty (CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
      context scope items code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil => exact ⟨CoupledTokenDiagnosticExtraction.nil (factory := factory) (nextCertificate _ scope code closed residual sourceSignatures declarations (by cases fuel <;> exact accepted))⟩

  | @uninitialized context nextContext binder rest declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CoupledTokenDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) origin.tail))⟩

  | @initialized context nextContext binder initializer initializerNode rest declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped
      exact ⟨CoupledTokenDiagnosticExtraction.initialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) origin.tail))⟩

  | @discard context expression expressionNode rest found typed syntaxTree remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨CoupledTokenDiagnosticExtraction.discard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations generatedBody bodyTyped origin.tail))⟩

  | @assign context assignment operator rhs rest sourceTyped writable rightTyped profile children remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel source scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root) (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CoupledTokenDiagnosticExtraction.assign (factory := factory) head parentSite origin.operand sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations generatedBody (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

  | @bitNot context assignment rest writable bare profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨CoupledTokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin) sameToken (Classical.choice (ih closed residual sourceSignatures declarations generatedBody
        (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
/-! The original imperative syntax/compiler induction retains local native
expression witnesses from the same enclosing emitted code. Lexical leaves and
match scrutinees use the actual native collectors; installed while/for closures
supply their raw condition typing by removal of the two administrative entries.
Actual assignment keys and present right-hand sides derive their local
native witnesses internally from the same code. For-post lexical children use
the same actual enclosing-code inversion as ordinary initializers/discards.
Source facts,
allocator identity, ordered occurrences and diagnostics remain unchanged.
This module constructs static extraction receipts, not a semantic E/F law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
open Core Frontend SourceInference GenericImperativeMatch
open TypedImperativeFor (Accepted InitialAccepted)
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

variable {matchCompilation : SourceCoreCompatibleDataMatches.Context}

private theorem unary_read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem unary_ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

private theorem iterate_condition {definitions : DataEnvironment} {context : Core.Context}
    {type : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) definitions) :
    HasType context condition (LanguageResult.resultType .bool) definitions := by
  have installed := TypedImperativeFor.Native.installed_body typed
  have conditionTyped := (TypedLexicalWhile.Native.conditional_inv installed).1
  exact TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front conditionTyped)

variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Actual compiler acceptance and one enclosing native typing traverse the
same position. Every actual expression callback receives its literal raw
witness, including the original ordered assignment keys and present RHS. -/
theorem extraction_of_typed_position_with_catalog_coupled (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)

    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor tracked policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
      context scope position expected type code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
  | body syntaxTree => exact ⟨CatalogCoupledExtractionFor.body (factory := factory) syntaxTree (CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped)⟩
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CatalogCoupledExtractionFor.uninitialized (factory := factory) found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initialized (factory := factory) found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped)
        allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
        exact ⟨CatalogCoupledExtractionFor.discard (factory := factory) found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated discardedTyped)
          (Classical.choice (ih closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

  | @block context mode id node statements rest expected found form _ inner remaining innerIH restIH
  | @scopedBlock context mode id node statements rest expected found form inner remaining innerIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact ⟨CatalogCoupledExtractionFor.block (factory := factory) found form (Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      let child := Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      exact ⟨CatalogCoupledExtractionFor.terminalBlock (factory := factory) exactUnique found form child stops issued⟩

  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
      let left := Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)
      let right := Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)
      let conditionTree := expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      exact ⟨CatalogCoupledExtractionFor.terminalIf (factory := factory) exactUnique found form conditionFound conditionType conditionTree left right thenStops elseStops issued⟩

  | @breaking context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨CatalogCoupledExtractionFor.breaking (factory := factory) found form⟩
  | @continuing context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨CatalogCoupledExtractionFor.continuing (factory := factory) found form⟩
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      have conditionNative := iterate_condition loopTyped
      exact ⟨CatalogCoupledExtractionFor.whileLoop (factory := factory) found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
        (Classical.choice (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped))
        loopTyped
        (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile children remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel source scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.assign (factory := factory) found form head (.occurrence id.occurrence) (AssignmentDiagnosticOrigins.OccursFor.statement found form) sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped)))⟩

  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initial remaining initialIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      refine ⟨CatalogCoupledExtractionFor.forLoop (factory := factory) found form ?_ ?_⟩
      · apply Classical.choice
        apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start found form, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (unary_ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    have conditionNative := iterate_condition loopTyped
    exact ⟨CatalogCoupledExtractionFor.initializersDone (factory := factory) conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated conditionNative)
      (Classical.choice (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped))
      (Classical.choice (CallableIndexedOwnedPreparedNativeForHeaderCollectors.extraction_of_lowerForItems_with_coupled residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped origin.post_origin))
      loopTyped⟩
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration monomorphic extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CatalogCoupledExtractionFor.initializerUninitialized (factory := factory) monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped
      exact ⟨CatalogCoupledExtractionFor.initializerInitialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxTree remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initializerDiscard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ bodyTyped))⟩
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile children remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression headerFuel source scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root) (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initializerAssign (factory := factory) head parentSite origin.header.operand sameToken sourceTyped rightTyped profile headerFuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩

  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨CatalogCoupledExtractionFor.bitNot (factory := factory) found form head writable bare profile (.occurrence id.occurrence) (EmittedDiagnosticTokenPlan.UnaryOccursFor.statement found form) sameToken (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody
        (TypedImperative.Native.execute_continuation nativeTyped)))⟩
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases generated
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at generated
      obtain ⟨body, generatedBody, generated⟩ := bind_ok generated
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile generated
      exact ⟨CatalogCoupledExtractionFor.initializerBitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin.header) sameToken (Classical.choice (ih closed residual sourceSignatures declarations projection
        ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩


  | @matchWith context mode id node resolution scrutineeNode rest expected control caseFacts
      found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary children remaining childIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨matchedType, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType childTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped) generatedMatch matchedTyped
      refine ⟨CatalogCoupledExtractionFor.matchWith (factory := factory) found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary) ?_ ?_ rfl sourceSignatures⟩
      · intro request member childContext selectedContext
        apply Classical.choice
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations :=
          matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
        exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)


  | @terminalMatch context mode id node resolution scrutineeNode rest expected control caseFacts
      exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary children stops childIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨matchedType, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType childTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped) generatedMatch matchedTyped
      let descendants : ∀ request, request ∈ requests → ∀ childContext,
          GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
          CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
            childContext request.scope (.statements false request.statements) expected type request.code :=
        fun request member childContext selectedContext => Classical.choice (by
          obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
          have childDeclarations :=
            matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
          obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
          exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
            (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped)
      have issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedBody
      let ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary
      exact ⟨CatalogCoupledExtractionFor.terminalMatch (factory := factory) exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt ordinary descendants stops issued rfl sourceSignatures⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
/-! Direct positive closure leaves retain their real compiler body and static
qualification. Their function model uses the Code's projection and runtime
receipt directly. No universal assignment diagnostic law is required to store
or form a closure. Global and builtin leaves retain their existing authority.
Neither a legacy closure leaf nor a native type manufactures this packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}

/-- Static qualification belongs to this exact prepared Support and Code. The
body registry indices concern global/builtin authority only. -/
inductive Association
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
      (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
      (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
      (qualified : qualification.ordinary code support)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association qualification headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
      (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
      (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
      (qualified : qualification.principal code support)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association qualification headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- Only captures and runtime typing change under actual map/world growth. -/
def Association.extend
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association qualification headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  cases association with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prepared qualified
      prefixContext globals referenceIndex (typed.weaken worlds)
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    exact .principal owner (captured.extend maps worlds) code history support origin prepared qualified
      globals leading referenceIndex (typed.weaken worlds)

theorem Association.source_binders
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) = function.parameters.map (fun binder => binder.scheme.body) := by
  cases association with
  | ordinary _ captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ captured code history support origin prepared qualified globals leading referenceIndex typed =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.source_ids
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.id) = function.parameters.map (fun binder => binder.id) := by
  cases association with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.id))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.id))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.result_core
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project function.resultType = .ok result := by
  cases association with
  | ordinary _ _ _ _ support _ _ _ _ _ _ _ => exact support.body.projection
  | principal _ _ _ _ support _ _ _ _ _ _ _ => exact support.body.projection

/-- The elementary lambda representation retains captures, Code and history;
it has no body or diagnostic field. This is a constructive forward projection. -/
theorem Association.lambda_represents
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) := by
  cases association with
  | ordinary _ captured code history _ _ _ _ _ _ _ typed => exact .lambda captured code history typed
  | principal _ captured code history _ _ _ _ _ _ _ typed => exact .lambda captured code history typed

theorem Association.native_type
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    native.type = CallableContract.functionType parameter result := by
  cases association with
  | ordinary _ _ _ _ _ _ _ _ _ _ _ typed => exact typed.type_eq
  | principal _ _ _ _ _ _ _ _ _ _ _ typed => exact typed.type_eq

/-- The literal Site binder policy and its real Source extension determine the
binder projections; the old diagnostic-bearing support is never built. -/
theorem Association.projected_bindings
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases association with
  | ordinary _ _ _ _ _ _ prepared _ _ _ _ _ =>
    cases prepared with
    | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
      exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended
  | principal _ _ _ _ _ _ prepared _ _ _ _ _ =>
    cases prepared with
    | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView environment =>
      exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

theorem Association.parameter_core
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  have projected := association.projected_bindings
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile projected support.body.projection
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile projected support.body.projection

end Members

abbrev StaticMember
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem StaticMember.extend
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember qualification headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

theorem StaticMember.source_binders
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) = function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.source_ids
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.id) = function.parameters.map (fun binder => binder.id) := by
  obtain ⟨association⟩ := member
  exact association.source_ids

theorem StaticMember.result_core
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project function.resultType = .ok result := by
  obtain ⟨association⟩ := member
  exact association.result_core

theorem StaticMember.native_type
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    native.type = CallableContract.functionType parameter result := by
  obtain ⟨association⟩ := member
  exact association.native_type

theorem StaticMember.projected_bindings
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Members

inductive FunctionOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.global function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType (.builtin function) native type

/-- Closure facts are proved from the retained Code and runtime receipt. The
receiving registry remains independent; no legacy closure model is projected. -/
def functions
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins qualification headers keys bodyRegistry faults mapping world
  projection := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure member =>
      obtain ⟨association⟩ := member
      cases association with
      | ordinary _ _ code _ _ _ _ _ _ _ _ _ => exact code.projection
      | principal _ _ code _ _ _ _ _ _ _ _ _ => exact code.projection
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) related
  runtime_hasType := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure member =>
      obtain ⟨association⟩ := member
      cases association with
      | ordinary _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
      | principal _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) related
  source_function := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure => exact .closure _
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) related
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related => exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)
    | builtin related => exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)

theorem FunctionOrigins.lambda_represents
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases origin with
  | closure member =>
    obtain ⟨association⟩ := member
    exact association.lambda_represents
  | global related => exact related.forget
  | builtin related => exact related.forget

theorem observations (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions qualification headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry)
    origin.lambda_represents

theorem runtime_views (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions qualification headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry)
    origin.lambda_represents

abbrev PayloadOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

section Outputs
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) :=
  .function (.closure member)

theorem closure_member
    (origin : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | closure member => intro function same; cases same; exact ⟨_, _, _, member, rfl⟩
    | global related => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Outputs

/-- The original reached state retains direct cells and the represented result.
No additional body or completion premise is installed in this postcondition. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context) (qualification : Facet compiled)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty) (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins qualification headers keys bodyRegistry registry faults profile index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
/-! Actual native typing supplies each ordered key witness. The absent RHS
remains a literal Unit and never becomes a Source expression certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates
open CompatibleProjectedBitNotStatements CallableIndexedOwnedPreparedNativeAssignmentChildren

theorem Head.of_lower_with_raw_occurrences {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidUnary : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (projected : assignment.target.projections ≠ [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered →
      RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression definitions →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalidProjection invalidUnary missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment,
      code = head.emit next output ∧ head.invalid = invalidUnary ∧
        head.PreparedAt site fuel invalidProjection missing := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      obtain ⟨_rhsRaw, ⟨packedResult, packedNative⟩⟩ := execute_children typed
      obtain ⟨sourceTypes, tree, keyTypes⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentChildren.keys_of_generated path generated packedNative extract
      obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl
        (sourceTyped binder description.binding) tree
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
          0 prepared.steps prepared.keys leaf := rootEq ▸ path
      have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
          assignment.target prepared codes sourceTypes leaf administrative .unit := by
        refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
          CompatiblePlaceHelperTyping.getter_of_execute typed,
          CompatiblePlaceHelperTyping.setter_of_execute_rhs typed
            (CompatiblePlaceHelperTyping.rhs_shift_typed_rhs (LanguageResult.success_hasType .unit))⟩
        · rw [← values.checked.catalog.project_runtimeType leaf, description.selectedType,
            values.checked.catalog.project_runtimeType, routeEq]
          exact description.leafProjected
        · intro k v declared
          rw [routeEq]
          exact description.virtual k v (rootEq.symm.trans declared)
        · intro empty
          have length := PreparedPath.steps_length path
          rw [empty, List.length_nil] at length
          exact projected (List.eq_nil_of_length_eq_zero length.symm)
      have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
        intro notMapping
        rw [routeEq]
        exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))
      refine ⟨⟨prepared, index, codes, leaf, sourceTypes, site, invalidUnary, layout, ordinary,
        by simpa only [routeEq] using lookup, rootEq ▸ writable binder description.binding, leafView ▸ profile⟩,
        by simp [Head.emit, routeEq], rfl, ?_⟩
      exact ⟨rfl, route, described, preparedBy⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
/-! Actual lowered for-header items retain original Source children, exact
allocations and bare assignment heads at their reached lexical context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedBranchingTree
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates


private theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource}
  {roots : List NodeId} {changed : List ExpressionId}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {initial : SourceSemantics.Context}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

theorem collected
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (syntaxTree : GenericForHeader.PreparedSyntax source expressionSyntax context items)
    (shape : ItemShape items)
    {faults : FunctionCalls.FaultRep}
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ items.flatMap ForItemForm.references, Reaches source roots id)
    {fuel : Nat} {type : Ty} {code : Expr} {nativeType : Ty} {parentSite : SourceCoreElaboration.ErrorSite}
    (operands : ∀ {assignment operator rhs}, .assignValue assignment operator rhs ∈ items →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand parentSite assignment.target.root operator))
    (unary : ∀ {assignment}, .assignBitNot assignment ∈ items → assignment.target.type = .word →
      faults (.invalidUnaryOperand .bitNot) (invalidUnary parentSite assignment.target.root))
    (origins : ∀ {assignment operator rhs}, .assignValue assignment operator rhs ∈ items →
      AssignmentDiagnosticOrigins.Occurs source parentSite assignment operator rhs)
    (unaryOrigins : ∀ {assignment}, .assignBitNot assignment ∈ items →
      GenericAssignmentUnaryDiagnostics.UnaryOccurs source parentSite assignment)
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel view scope items type reasonAt
      (fun _ => pure (LocalLoop.fallthrough type)) = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source
      (TypedCertificate source certificates) definitions administrative type (TypedForHeader.Fallthrough type)
      context scope items code, ∀ registry, PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault registry faults tree := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil =>
    have same : code = LocalLoop.fallthrough type := by cases fuel <;> exact (Except.ok.inj accepted).symm
    exact ⟨.nil same, fun _ => .nil (next := same)⟩
  | @uninitialized context nextContext binder rest declaration mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.absentRequest view scope binder payload)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.absentRequest view scope binder payload) edited.metadata.symm annotation
      obtain ⟨tail, tailSites⟩ := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended)
        (fun child member => reached child (by simpa [ForItemForm.references] using member))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member))
        generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      refine ⟨.uninitialized mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail, ?_⟩
      intro registry
      exact .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary)
        (projected := binder_projected (binderPolicy scope binder mono ▸ projected))
        (allocation := originalAllocation) (annotation := originalAnnotation)
        (same := by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same)
        (remaining := tail) (tailSites registry)
  | @initialized context nextContext binder initializer initializerNode rest declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      obtain ⟨tail, tailSites⟩ := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended)
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member))
        generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      refine ⟨.initialized mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail, ?_⟩
      intro registry
      exact .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary)
        (initializerFound := initializerFound) (sourceType := sourceType) (initial := value)
        (allocation := originalAllocation) (annotation := originalAnnotation)
        (same := by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same)
        (remaining := tail) (tailSites registry)
  | @discard context expression expressionNode rest found typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
      obtain ⟨tail, tailSites⟩ := ih shape.discard_tail fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member)) generatedBody tailTyped
      refine ⟨.discard found
        ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩
        tail, ?_⟩
      intro registry
      exact .discard (found := found)
        (value := ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩)
        (remaining := tail) (tailSites registry)
  | @assign context assignment operator rhs rest sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sourceProfile, restShape⟩ := shape.assignment_tail
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root)
          (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        have edge : .expression child ∈ assignment.references ++ [.expression rhs] := by
          rcases List.mem_cons.mp member with equal | member
          · subst child; simp
          · exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member)
        exact reached _ (by simp only [List.flatMap_cons, ForItemForm.references]; exact List.mem_append_left _ edge)
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child (List.mem_cons_of_mem _ member)))).trans compiled
      obtain ⟨originalHead, emittedOriginal, sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emittedOriginal]
      obtain ⟨tail, tailSites⟩ := ih restShape fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member)) generatedBody
        (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))
      refine ⟨.assign originalHead tail, ?_⟩
      intro registry
      exact .assign (head := originalHead) (remaining := tail) (tailSites registry)
        (CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
          (origins List.mem_cons_self) sourceSignatures preparedAt (sameToken.symm ▸ operands List.mem_cons_self sourceProfile) registry)
  | @bitNot context assignment rest writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.bitNot_tail bare
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder found => writable binder ((rootBinder edited.metadata _).trans found))
        bare profile accepted
      rw [emitted]
      obtain ⟨tail, tailSites⟩ := ih restShape fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp only [List.flatMap_cons]; exact List.mem_append_right _ member))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member)) generatedBody
        (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped))
      refine ⟨.bitNot head tail, fun registry => .bitNot (tailSites registry) ?_⟩
      simpa only [CompatibleBitNotStatements.Head.Errors, token] using unary List.mem_cons_self rawWord

  | @bitNotProjected context assignment rest sourceTyped writable projected profile childSyntax remaining ih =>
    obtain ⟨_rawWord, restShape⟩ := shape.unary_tail
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, compiled⟩ := bind_ok accepted
      have accessible : ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        exact reached _ (by
          simp only [List.flatMap_cons, ForItemForm.references]
          exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member))
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child member))).trans compiled
      obtain ⟨head, emitted, _sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable projected profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emitted]
      obtain ⟨tail, tailSites⟩ := ih restShape fields closed residual sourceSignatures declarations
        (fun child member => reached child (List.mem_append_right _ member))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        (fun member => origins (List.mem_cons_of_mem _ member))
        (fun member => unaryOrigins (List.mem_cons_of_mem _ member)) generatedBody
        (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped))
      exact ⟨.bitNotProjected head tail, fun registry =>
        .bitNotProjected (tailSites registry) (.projected (unaryOrigins List.mem_cons_self)
          sourceSignatures projected preparedAt)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
/-! The actual compiler flow and its native typing produce the original scoped
branch and assignment tree. Only reached expression metadata is transported; allocations
and assignment heads keep their exact emitted Core expressions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedBranchingTree
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates
open CallableIndexedOwnedPreparedBranchingCatalogSites (Collected)

private theorem statement_identity {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    GenericLexicalStatements.StatementSourceIdentity source view := by
  refine ⟨metadata.owner, metadata.inputs, metadata.roots, ?_⟩
  intro id
  cases found : source.lookupStatement? id with
  | some node => exact (metadata.symm.statement found).symm
  | none =>
    cases viewed : view.lookupStatement? id with
    | none => rfl
    | some node => have impossible := metadata.statement viewed; rw [found] at impossible; cases impossible

private theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

private theorem while_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) result definitions) :
    ∃ conditionType, HasType context condition conditionType definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨_, shifted⟩ := computation_child loop
              exact ⟨_, TypedLexicalWhile.Native.remove_front
                (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem binders_fields {owner : Resolved.DeclarationId}
    {parent child : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend owner parent binders child) :
    Dynamic.RuntimeContextFields parent child := by
  induction extended with
  | nil => exact .refl _
  | cons head _ ih => exact (Dynamic.RuntimeContextFields.ofBinderExtends head).trans ih

/-- Native typing of the actual hidden allocation retains the exact evaluated
scrutinee callback, before any matcher or arm body executes. -/
private theorem match_expression
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} {administrative : Core.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {before after : CompatibleMatchCertificates.ExpressionCertificate}
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {code : Expr}
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason before bodyCertificate code)
    {type : Ty} (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions)
    (convert : ∀ lowered, before scope resolution.scrutinee lowered →
      (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions) → after scope resolution.scrutinee lowered) :
    CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason after bodyCertificate code := by
  cases receipt with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    apply CompatibleMatchCertificates.Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
      scrutineeOwned found projection _ sameType arms fallback branches hiddenCompiled
    have native := hiddenCompiled
    rw [allocator] at native
    unfold SourceCoreSourceCells.letInitialized at native
    obtain ⟨allocation, allocated, exactCode⟩ := bind_ok native
    cases exactCode
    cases typed with
    | caseE initial failure next => exact convert _ expression ⟨_, initial⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource}
  {roots : List NodeId} {changed : List ExpressionId}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {initial : SourceSemantics.Context}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Every callback is reached from the original body. Header references include
all remaining initializers, the actual test, the post items and the loop body. -/
def PositionReaches (source : TypedSource) (roots : List NodeId) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => ∀ id ∈ statements, Reaches source roots (.statement id)
  | .initializers items condition post statements =>
      ∀ id ∈ items.flatMap ForItemForm.references ++ [.expression condition] ++
        post.flatMap ForItemForm.references ++ statements.map NodeId.statement,
        Reaches source roots id

/-- The for-header continuation is recovered from the actual outer compiler
call. Its condition, post and body equations are retained together. -/
def CompilerAccepted (policy : SourceCoreLoops.Policy) (fuel : Nat) (original source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (position : GenericImperativeMatch.Position)
    (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  match position with
  | .statements mode statements =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code
  | .initializers items condition post statements =>
      ∃ headerFuel parentSite next,
        AssignmentDiagnosticOrigins.ForOrigin original parentSite items condition post statements ∧
        SourceCoreLoops.lowerForItems policy parentSite headerFuel source scope items type reasonAt next = .ok code ∧
        ∀ loopScope nextCode, next loopScope = .ok nextCode →
          ∃ conditionCode loopCode postCode,
            policy.lowerExpression fuel source loopScope condition reasonAt = .ok conditionCode ∧
            conditionCode.type = .bool ∧
            SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source loopScope statements type reasonAt false selfReason = .ok loopCode ∧
            SourceCoreLoops.lowerForItems policy parentSite fuel source loopScope post type reasonAt
              (fun _ => pure (LocalLoop.fallthrough type)) = .ok postCode ∧
            nextCode = LocalLoop.iterate type conditionCode.expression loopCode postCode selfReason

private theorem iterate_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    ∃ conditionType, HasType context condition conditionType definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨_, shifted⟩ := computation_child loop
              exact ⟨_, TypedLexicalWhile.Native.remove_front
                (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem header_operand {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {items : List ForItemForm} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.HeaderOrigin source site items)
    (member : .assignValue assignment operator rhs ∈ items) :
    AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs := by
  rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩ |
    ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩
  · exact .header found form (List.mem_append_left _ (List.mem_append_right _ member))
  · exact .header found form (List.mem_append_right _ (List.mem_append_right _ member))

private theorem header_unary {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {items : List ForItemForm} {assignment : AssignmentResolution}
    (origin : AssignmentDiagnosticOrigins.HeaderOrigin source site items)
    (member : .assignBitNot assignment ∈ items) :
    GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment := by
  rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩ |
    ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩
  · exact .header found form (List.mem_append_left _ (List.mem_append_right _ member))
  · exact .header found form (List.mem_append_right _ (List.mem_append_right _ member))

theorem collected_at
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root))
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (ledger : initial.solvedRequirements = matchCompilation.solvedRequirements)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax source expressionSyntax context position expected)
    (shape : PositionShape source position)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : PositionReaches source roots position)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : CompilerAccepted policy fuel source view scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      position expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | body body =>
    have viewed := CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique
      (fun _ _ original => original) body reached
    have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual _
      readPolicy binderPolicy allocationPolicy
      (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields initial context →
        Reaches source roots (.expression id) → TypedCertificate source certificates context scope id lowered)
      (fun context _ _ _ scope fuel id node lowered declarations syntaxValue found typed generated nativeType typedNative contextFields reachable => by
        have originalFound : source.lookupExpression? id = some node := (expression_lookup edited avoids reachable).trans found
        have originalTyped := CallableLambdaViewStaticTyping.expression_original edited avoids unique typed reachable
        exact ⟨node, originalFound, originalTyped, children context contextFields
          (scope_declarations edited.metadata.symm declarations) syntaxValue reachable originalFound originalTyped generated typedNative⟩)
      viewed closed residual sourceSignatures (scope_declarations edited.metadata declarations) projection accepted nativeTyped
    have discharged := CallableIndexedOwnedPreparedLexicalContextCertificates.Tree.discharge_context extracted fields
    have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
    exact .body body (CallableLambdaViewBodyTree.transport reverse (avoids.view edited.metadata)
      (fun _ _ _ _ accessible value => value (accessible.metadata edited.metadata.symm)) discharged
      (fun id member => (reached id member).metadata edited.metadata))
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.absentRequest view scope binder payload)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.absentRequest view scope binder payload) edited.metadata.symm annotation
      have tail := ih (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .uninitialized found form mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      have tail := ih (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initialized found form mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨_continuing, restShape⟩ := shape.discard_tail found form notTail
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      obtain ⟨body, generatedBody, sameCode⟩ : ∃ body,
          SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope rest type reasonAt mode selfReason = .ok body ∧
          code = LocalSequence.discard (LocalLoop.controlType type) lowered.expression body := by
        cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
        all_goals
          obtain ⟨checked, _, accepted⟩ := bind_ok accepted
          cases checked
          obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
          exact ⟨body, generatedBody, (Except.ok.inj accepted).symm⟩
      subst code
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      exact .discard found form notTail expressionFound
        ⟨expressionNode, expressionFound, typed, children context fields declarations syntaxValue accessible expressionFound typed generated childTyped⟩
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sourceProfile, restShape⟩ := shape.assignment_tail found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        have edge : .expression child ∈ assignment.references ++ [.expression rhs] := by
          rcases List.mem_cons.mp member with equal | member
          · subst child; simp
          · exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member)
        exact .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using edge)
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child (List.mem_cons_of_mem _ member)))).trans compiled
      obtain ⟨originalHead, emittedOriginal, sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emittedOriginal]
      exact .assignPrepared found form originalHead
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))) (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site (.statement found form) sourceSignatures preparedAt
            (sameToken.symm ▸ operands (.statement found form) sourceProfile) registry)
  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH
  | @scopedBlock context mode id node statements rest expected found form inner remaining innerIH restIH =>
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    have innerReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form
        (innerIH innerShape fields closed residual sourceSignatures declarations innerReached projection generatedInner innerTyped)
        (restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    have innerReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .terminalBlock exactUnique found form
        (innerIH innerShape fields closed residual sourceSignatures declarations innerReached projection generatedInner innerTyped)
        stops ((GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix).transport (statement_identity edited.metadata.symm))
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have thenReached : ∀ child ∈ thenBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    have elseReached : ∀ child ∈ elseBody.getD [], Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by cases elseBody <;> simp_all [StatementForm.references])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
          (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH restShape fields closed residual sourceSignatures declarations
            (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
          (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH restShape fields closed residual sourceSignatures declarations
            (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have thenReached : ∀ child ∈ thenBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    have elseReached : ∀ child ∈ elseBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      exact .terminalIf exactUnique found form conditionFound conditionType
        ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
        (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
        (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
        thenStops elseStops ((GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix).transport (statement_identity edited.metadata.symm))
  | breaking found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .breaking found form
  | continuing found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .continuing found form
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    obtain ⟨loopShape, restShape⟩ := shape.loop found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have loopReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, conditionTyped⟩ := while_condition loopTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact .whileLoop found form conditionFound conditionType
        ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
        (loopIH loopShape fields closed residual sourceSignatures declarations loopReached projection generatedLoop loopBodyTyped)
        loopTyped
        (restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @matchWith context mode id node resolution scrutineeNode rest expected control caseFacts
      found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary childrenSyntax remaining childIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, rawReceipt, _, generatedChildren⟩ := CompatibleMatchNativeReceipts.finite_typed_of_lower
        onError matchAllocator matchDefinitions
        (expressionCertificate := fun scope id lowered => ∃ childFuel,
          policy.lowerExpression childFuel view scope id reasonAt = .ok lowered)
        (fun childFuel lowered generated => ⟨childFuel, generated⟩) generatedMatch matchedTyped
      have refs : ∀ child ∈ resolution.references, Reaches source roots child :=
        fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
      have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
      have certified := match_expression onError matchAllocator rawReceipt matchedTyped
        (after := TypedCertificate source certificates context)
        (fun lowered generated native => by
          obtain ⟨childFuel, generated⟩ := generated
          obtain ⟨nativeType, native⟩ := native
          exact ⟨scrutineeNode, scrutineeFound, scrutineeTyped, children context fields declarations
            scrutineeSyntax scrutineeReached scrutineeFound scrutineeTyped generated native⟩)
      have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
      have receipt := CallableLambdaViewMatchRuntimeCertificates.match_certificate reverse
        (avoids.view edited.metadata) matchAllocator (fun _ _ _ _ value => value) certified
        (scrutineeReached.metadata edited.metadata)
      apply Collected.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped
        matchCompilation matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary)
      · intro request member childContext related
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations := related.source_declarations found form (hidden found form) declarations
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := related.closed_fields
        have childFields : Dynamic.RuntimeContextFields context childContext := by
          cases related with
          | arm _ _ _ extended _ => exact binders_fields extended
          | default _ _ => exact .refl _
        apply childIH request childContext related.forget (shape.match_request found form related.forget)
          (fields.trans childFields) (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations
        · intro statement present
          apply refs
          cases related with
          | arm armMember sameBody _ _ _ =>
            simp only [MatchResolution.references, List.mem_cons, reduceCtorEq, List.mem_append]
            exact .inl (.inr (List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩))
          | default sameBody _ =>
            simp [MatchResolution.references, sameBody, present]
        · exact projection
        · exact generated
        · exact childTyped
      · exact restIH (shape.match_children found form).2.2 fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped
      · exact catalog
      · exact ⟨by simpa only [SourceCoreCompatibleDataMatches.Context.signatures, SourceCoreCompatibleDataMatches.Context.checked, matchValues] using sourceSignatures,
          fields.solvedRequirements.trans ledger⟩
  | @terminalMatch context mode id node resolution scrutineeNode rest expected control caseFacts
      exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary childrenSyntax stops childIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, rawReceipt, _, generatedChildren⟩ := CompatibleMatchNativeReceipts.finite_typed_of_lower
        onError matchAllocator matchDefinitions
        (expressionCertificate := fun scope id lowered => ∃ childFuel,
          policy.lowerExpression childFuel view scope id reasonAt = .ok lowered)
        (fun childFuel lowered generated => ⟨childFuel, generated⟩) generatedMatch matchedTyped
      have refs : ∀ child ∈ resolution.references, Reaches source roots child :=
        fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
      have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
      have certified := match_expression onError matchAllocator rawReceipt matchedTyped
        (after := TypedCertificate source certificates context)
        (fun lowered generated native => by
          obtain ⟨childFuel, generated⟩ := generated
          obtain ⟨nativeType, native⟩ := native
          exact ⟨scrutineeNode, scrutineeFound, scrutineeTyped, children context fields declarations
            scrutineeSyntax scrutineeReached scrutineeFound scrutineeTyped generated native⟩)
      have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
      have receipt := CallableLambdaViewMatchRuntimeCertificates.match_certificate reverse
        (avoids.view edited.metadata) matchAllocator (fun _ _ _ _ value => value) certified
        (scrutineeReached.metadata edited.metadata)
      apply Collected.terminalMatch exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped
        matchCompilation matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary)
      · intro request member childContext related
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations := related.source_declarations found form (hidden found form) declarations
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := related.closed_fields
        have childFields : Dynamic.RuntimeContextFields context childContext := by
          cases related with
          | arm _ _ _ extended _ => exact binders_fields extended
          | default _ _ => exact .refl _
        apply childIH request childContext related.forget (shape.match_request found form related.forget)
          (fields.trans childFields) (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations
        · intro statement present
          apply refs
          cases related with
          | arm armMember sameBody _ _ _ =>
            simp only [MatchResolution.references, List.mem_cons, reduceCtorEq, List.mem_append]
            exact .inl (.inr (List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩))
          | default sameBody _ =>
            simp [MatchResolution.references, sameBody, present]
        · exact projection
        · exact generated
        · exact childTyped
      · exact stops
      · exact (GenericLexicalStatements.IssuedSuffix.of_accepted generatedBody).transport
          (statement_identity edited.metadata.symm)
      · exact catalog
      · exact ⟨by simpa only [SourceCoreCompatibleDataMatches.Context.signatures, SourceCoreCompatibleDataMatches.Context.checked, matchValues] using sourceSignatures,
          fields.solvedRequirements.trans ledger⟩
  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.bitNot_tail found form bare
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder binding => writable binder ((rootBinder edited.metadata _).trans binding))
        bare profile accepted
      rw [emitted]
      exact .bitNot found form head
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (by simpa only [CompatibleBitNotStatements.Head.Errors, token] using unary (.statement found form) rawWord)
  | @bitNotProjected context mode id node assignment rest expected found form sourceTyped writable projected profile childSyntax remaining ih =>
    obtain ⟨_rawWord, restShape⟩ := shape.unary_tail found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, generatedBody, compiled⟩ := bind_ok accepted
      have accessible : ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        exact .statement (reached id List.mem_cons_self) found
          (by simpa only [form, StatementForm.references, AssignmentResolution.references,
            PlaceResolution.references] using CallableLambdaViewPlaceLowering.key_reference member)
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child member))).trans compiled
      obtain ⟨head, emitted, _sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable projected profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, childNode, childFound, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨childNode, childFound, childNode, childFound, typed,
              children context fields declarations approved (accessible child member) childFound typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emitted]
      exact .bitNotProjected found form head
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (.projected (.statement found form) sourceSignatures projected preparedAt)
  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initialSyntax remaining initialIH restIH =>
    obtain ⟨initialShape, postShape, bodyShape, restShape⟩ := shape.for_children found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      apply Collected.forLoop found form
      · apply initialIH ⟨initialShape, postShape, bodyShape⟩ fields closed residual sourceSignatures declarations
        · intro child member
          exact .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
        · exact projection
        · refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start (tracked := true) found form, generatedInitial, ?_⟩
          intro loopScope nextCode generated
          obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
          obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
          cases checked
          obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
          obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
          cases generated
          exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (ensure_same conditionChecked).symm,
            loopGenerated, postGenerated, rfl⟩
        · exact initialTyped
      · exact restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    obtain ⟨_, conditionNative⟩ := iterate_condition loopTyped
    have accessible : Reaches source roots (.expression condition) := reached _ (by simp)
    obtain ⟨postTree, postSites⟩ := CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors.collected
      edited avoids unique binderPolicy allocationPolicy assignments unaryPolicy children postSyntax shape.2.1
      fields closed residual sourceSignatures declarations
      (fun child member => reached _ (by simp [member]))
      (fun member profile => operands (header_operand
        (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member) profile)
      (fun member rawWord => unary (header_unary
        (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member) rawWord)
      (fun member => header_operand (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member)
      (fun member => header_unary (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member)
      postGenerated postTyped
    refine Collected.initializersDone conditionFound conditionType
      ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax accessible conditionFound typed conditionGenerated conditionNative⟩
      ?_ postTree postSites loopTyped
    exact loopIH shape.2.2 fields closed residual sourceSignatures declarations
      (fun child member => reached _ (by simp [member])) projection loopGenerated bodyTyped
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration mono extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.absentRequest view scope binder payload)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.absentRequest view scope binder payload) edited.metadata.symm annotation
      have tail := ih ⟨shape.1.let_tail, shape.2⟩ (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended)
        (fun child member => reached child (by simpa [ForItemForm.references] using member))
        projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initializerUninitialized mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      have tail := ih ⟨shape.1.let_tail, shape.2⟩ (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended)
        (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member)))
        projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initializerInitialized mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxValue remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
      exact .initializerDiscard found
        ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩
        (ih ⟨shape.1.discard_tail, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member))) projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩ tailTyped)
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sourceProfile, restShape⟩ := shape.1.assignment_tail
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression headerFuel view scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root)
          (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        have edge : .expression child ∈ assignment.references ++ [.expression rhs] := by
          rcases List.mem_cons.mp member with equal | member
          · subst child; simp
          · exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member)
        exact reached _ (by simp only [List.flatMap_cons, ForItemForm.references, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_append.mp edge)))))
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := headerFuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child (List.mem_cons_of_mem _ member)))).trans compiled
      obtain ⟨originalHead, emittedOriginal, sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emittedOriginal]
      exact .initializerAssignPrepared originalHead
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member))) projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))) (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
            (AssignmentDiagnosticOrigins.HeaderOriginFor.operand (tracked := true) (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceSignatures preparedAt
            (sameToken.symm ▸ operands (AssignmentDiagnosticOrigins.HeaderOriginFor.operand (tracked := true) (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceProfile) registry)
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.1.bitNot_tail bare
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder binding => writable binder ((rootBinder edited.metadata _).trans binding))
        bare profile accepted
      rw [emitted]
      exact .initializerBitNot head
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using
            (List.mem_append_right (ForItemForm.references _) member))) projection
          ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin,
            generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (by simpa only [CompatibleBitNotStatements.Head.Errors, token] using (unary
          (AssignmentDiagnosticOrigins.HeaderOriginFor.unary (tracked := true)
            (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) rawWord))

  | @initializerBitNotProjected context assignment rest condition post statements expected sourceTyped writable projected profile childSyntax remaining ih =>
    obtain ⟨_rawWord, restShape⟩ := shape.1.unary_tail
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, compiled⟩ := bind_ok accepted
      have accessible : ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        apply reached
        simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (CallableLambdaViewPlaceLowering.key_reference member))))
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := headerFuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child member))).trans compiled
      obtain ⟨head, emitted, _sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable projected profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, childNode, childFound, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨childNode, childFound, childNode, childFound, typed,
              children context fields declarations approved (accessible child member) childFound typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emitted]
      exact .initializerBitNotProjected head
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using
            (List.mem_append_right (ForItemForm.references _) member))) projection
          ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin,
            generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (.projected (AssignmentDiagnosticOrigins.HeaderOriginFor.unary (tracked := true)
          (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceSignatures projected preparedAt)


theorem collected
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root))
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (ledger : initial.solvedRequirements = matchCompilation.solvedRequirements)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax source expressionSyntax context position expected)
    {mode : Bool} {statements : List StatementId} (atStatements : position = .statements mode statements)
    (shape : Shape source mode statements)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id))
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      (.statements mode statements) expected type code := by
  cases atStatements
  exact collected_at edited avoids unique readPolicy binderPolicy allocationPolicy assignments unaryPolicy operands unary
    matchPolicy matchValues matchDefinitions matchAllocator hidden catalog ledger children
    syntaxTree shape fields closed residual sourceSignatures declarations reached projection accepted nativeTyped

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
/-! The literal body recipe and one same-view compiler extraction construct
one JointBody with actual local native occurrence witnesses. Ordered assignment
keys and present RHS use the real execute inversion. The canonical transport,
chosen flow and prepared structural eliminator are the original producer's
same-Code proofs. There is no expected child typing supplier or semantic body
callback. The static child factory still must manufacture the genuine finite
compiler certificate at each actual Source occurrence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability CallableLambdaViewStaticTyping
open GenericImperativeMatch
open CallableIndexedOwnedContextualLambdaJointStaticReceipts

section Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Static policy belongs to this exact body lowerer. The single expression
factory receives the actual local native witness, including ordered keys and
present RHS. No expected child typing or expression execution is supplied. -/
structure NativeExtractionInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
    source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType definitions → certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

/-- The real occurrence collector runs once at this actual accepted view flow. -/
theorem NativeExtractionInputs.extract {residualMode : Bool} {policy : SourceCoreLoops.Policy}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (inputs : NativeExtractionInputs (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (reasonAt := reasonAt)
      (definitions := definitions) (administrative := administrative) (invalidOperand := invalidOperand)
      (invalidUnary := invalidUnary) (invalidProjection := invalidProjection) (missingDefault := missingDefault)
      residualMode policy context scope)
    (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {position : Position} {expected : TypeSystem.Ty} {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor true policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
      (trackedFactory diagnosticPolicy source invalidOperand) invalidUnary invalidProjection missingDefault expressionSyntax certificates
      definitions administrative inputs.matchCompilation.solvedRequirements context scope position expected type code) := by
  exact CallableIndexedOwnedPreparedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled residualMode diagnosticPolicy
    (trackedFactory diagnosticPolicy source invalidOperand) inputs.matchPolicy inputs.matchValues inputs.matchDefinitions
    inputs.matchAllocator inputs.matchChildStatic inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy
    inputs.expressions inputs.assignments inputs.unaries unique syntaxTree
    inputs.closed inputs.residual inputs.sourceSignatures inputs.declarations projection accepted nativeTyped

end Extraction

section Site
open CallableIndexedLambdaValues
open CallableIndexedLambdaGeneration
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

/-- One actual native-aware collector supplies the original joint constructor.
The real Site, compiler callback, body, lexical context, flow, prepared tree and
view transport remain exact. No arbitrary body equality or execution is input. -/
theorem at_site {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {captured : Dynamic.Environment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site compiled.indexed named parameters result statements sourceContext evidence captured scope administrative)
    (recipe : BodyRecipe namedCompilation site.code)
    (program : Program) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code)
    (frame : Dynamic.ClosureFrame program (CallableIndexedLambdaGeneration.closure named parameters result statements sourceContext evidence captured))
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (readFuel : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {changed : List ExpressionId}
    (edited : LocalView (CallableIndexedNamedGeneration.source named) site.code.view changed)
    (avoids : Avoids (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
    (sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements)
    (syntaxTransport : ∀ id, Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      expressionSyntax site.code.view id → expressionSyntax (CallableIndexedNamedGeneration.source named) id)
    (expressions : ∀ context scope id lowered,
      Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      certificates readFuel site.code.view context scope id lowered →
      certificates readFuel (CallableIndexedNamedGeneration.source named) context scope id lowered)
    (syntaxTree : Syntax (CallableIndexedNamedGeneration.source named)
      (expressionSyntax (CallableIndexedNamedGeneration.source named)) inputs.context (.statements true statements) result)
    (viewSyntax : Syntax site.code.view (expressionSyntax site.code.view) inputs.context (.statements true statements) result)
    (projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore)
    {residualMode : Bool}
    (static : NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (onError := site.code.allocationError) (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view) (certificates := certificates readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := invalidOperand) (invalidUnary := invalidUnary) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) residualMode (bodyPolicy namedCompilation site.code) inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope))
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ∃ body : JointBody namedCompilation site.code program expressionSyntax certificates diagnosticPolicy
        invalidOperand invalidUnary invalidProjection missingDefault,
      body.toBody.toContext = inputs ∧ body.readFuel = readFuel := by
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked) site.code (bodyPolicy namedCompilation site.code)
    (callback_of_recipe namedCompilation recipe)
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : site.code.receipt.body = CompatibleStatements.finish site.code.receipt.resultCore flow
      site.code.compilation.internalReason site.code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨nativeFlowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow (emitted ▸ nativeTyped)
  obtain ⟨actual⟩ := static.extract diagnosticPolicy (edited.metadata.unique unique) viewSyntax projection generated flowTyped
  have reverse : LocalView site.code.view (CallableIndexedNamedGeneration.source named) changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  obtain ⟨canonical, prepared⟩ := transport_prepared reverse (avoids.view edited.metadata)
    (edited.metadata.unique unique)
    (fun id reached receipt => syntaxTransport id (reached.metadata edited.metadata.symm) receipt)
    (fun context scope id lowered reached receipt => expressions context scope id lowered
      (reached.metadata edited.metadata.symm) receipt)
    (targetFactory := trackedFactory diagnosticPolicy (CallableIndexedNamedGeneration.source named) invalidOperand)
    (actual.eliminate static.ledger) (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have actualLedger : static.matchCompilation.solvedRequirements = inputs.context.solvedRequirements := static.ledger.symm
  exact ⟨{
    toBody := {
      toContext := inputs, frame := frame, readFuel := readFuel, flow := flow,
      projection := projection, emitted := emitted, tree := canonical,
      valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) site.code inputs frame sameLedger,
      unique := unique, syntaxTree := syntaxTree },
    recipe := recipe, generated := generated,
    actual := actualLedger ▸ actual,
    prepared := prepared }, rfl, rfl⟩

end Site

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBareImperativeCollectors
/-! The actual compiler flow and its native typing produce the original bare
assignment tree. Only reached expression metadata is transported; allocations
and assignment heads keep their exact emitted Core expressions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBareImperativeCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedBareAssignmentTree
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates

private theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource}
  {roots : List NodeId} {changed : List ExpressionId}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {initial : SourceSemantics.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Genuine Source syntax and one native body witness suffice for every
expression callback, including the RHS under the seven-slot assignment frame. -/
theorem tree
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context position expected)
    {statements : List StatementId} (atStatements : position = .statements true statements)
    (shape : Shape source statements)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id))
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope statements type reasonAt true selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      (.statements true statements) expected type code := by
  induction syntaxTree generalizing statements scope fuel code nativeType with
  | body body =>
    cases atStatements
    have viewed := CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique
      (fun _ _ original => original) body reached
    have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual true
      readPolicy binderPolicy allocationPolicy
      (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields initial context →
        Reaches source roots (.expression id) → TypedCertificate source certificates context scope id lowered)
      (fun context _ _ _ scope fuel id node lowered declarations syntaxValue found typed generated nativeType typedNative contextFields reachable => by
        have originalFound : source.lookupExpression? id = some node := (expression_lookup edited avoids reachable).trans found
        have originalTyped := CallableLambdaViewStaticTyping.expression_original edited avoids unique typed reachable
        exact ⟨node, originalFound, originalTyped, children context contextFields
          (scope_declarations edited.metadata.symm declarations) syntaxValue reachable originalFound originalTyped generated typedNative⟩)
      viewed closed residual sourceSignatures (scope_declarations edited.metadata declarations) projection accepted nativeTyped
    have discharged := CallableIndexedOwnedPreparedLexicalContextCertificates.Tree.discharge_context extracted fields
    have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
    exact .body body (CallableLambdaViewBodyTree.transport reverse (avoids.view edited.metadata)
      (fun _ _ _ _ accessible value => value (accessible.metadata edited.metadata.symm)) discharged
      (fun id member => (reached id member).metadata edited.metadata))
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.absentRequest view scope binder payload)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.absentRequest view scope binder payload) edited.metadata.symm annotation
      have tail := ih rfl (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .uninitialized found form mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      have tail := ih rfl (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initialized found form mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨same, restShape⟩ := shape.discard_tail found form notTail
      cases same
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      exact .discard found form notTail expressionFound
        ⟨expressionNode, expressionFound, typed, children context fields declarations syntaxValue accessible expressionFound typed generated childTyped⟩
        (ih rfl restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile childSyntax remaining ih =>
    cases atStatements
    obtain ⟨sameOperator, bare, restShape⟩ := shape.assign_tail found form
    cases sameOperator
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope (.occurrence id.occurrence)
          assignment .equal (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root .equal)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        simpa only [SourceCoreLoops.assignValue, assignments.equal] using accepted
      have accessible : Reaches source roots (.expression rhs) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      obtain ⟨rhsSyntax, rhsNode, rhsFound, rhsTyped⟩ := childSyntax rhs (by simp)
      obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot, _layout, generated, _sameType, _profile, codeEq⟩ :=
        CompatibleBareAssignment.of_lower bare compiled
      have rhsNative := CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_present_rhs
        (prepared := prepared) (reference := .var index) (keys := SourceCoreCalls.packArguments [])
        (rhs := value.expression) (next := body) (output := LocalLoop.controlType type) (result := nativeType)
        (operator := .equal) (codeEq ▸ nativeTyped)
      have rhsType : rhsNode.type = assignment.target.type := by
        obtain ⟨actualNode, contains, actualType⟩ := rightTyped.stored_type
        have sameNode := Option.some.inj (rhsFound.symm.trans (lookupExpression?_complete unique contains))
        exact sameNode ▸ actualType
      let originalHead : GenericAssignmentStatements.Head values source context
          (TypedCertificate source certificates context) scope administrative definitions assignment .equal rhs := {
        prepared := prepared
        index := index
        codes := []
        leaf := prepared.route.rootSourceType
        lowered := value
        node := rhsNode
        invalid := invalidOperand (.occurrence id.occurrence) assignment.target.root .equal
        shape := .bare bare _layout
        slot := _slot
        writable := _rootType ▸ writable binder ((rootBinder edited.metadata _).trans _binding)
        found := rhsFound
        right := ⟨rhsNode, rhsFound, rhsTyped, children context fields declarations rhsSyntax accessible rhsFound rhsTyped generated rhsNative⟩
        rightView := by simpa only [rhsType] using _rawView
        rightType := _sameType
        profile := .inl rfl }
      have emittedOriginal : code = originalHead.emit body (LocalLoop.controlType type) := codeEq
      rw [emittedOriginal]
      exact .assign found form originalHead
        (ih rfl restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped)))
  | block found form _ _ _ _ _ | terminalBlock _ found form _ _ _ _ | scopedBlock found form _ _ _ _ =>
    cases atStatements
    exact False.elim (shape.not_block found form)
  | ifThen found form _ _ _ _ _ _ _ _ _ _ _ | terminalIf _ found form _ _ _ _ _ _ _ _ _ _ _ =>
    cases atStatements
    exact False.elim (shape.not_if found form)
  | breaking found form | continuing found form =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | whileLoop found form _ _ _ _ _ _ _ _ | forLoop found form _ _ _ _ _
  | bitNot found form _ _ _ _ _ | matchWith found form _ _ _ _ _ _ _ _ _ _ _ _
  | terminalMatch _ found form _ _ _ _ _ _ _ _ _ _ _ =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard
  | initializerAssign | initializerBitNot => cases atStatements

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBareImperativeCollectors
end
