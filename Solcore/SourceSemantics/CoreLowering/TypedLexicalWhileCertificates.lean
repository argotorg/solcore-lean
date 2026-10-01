import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileTree
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.LoopSourceInduction

/-! Static shape and native typing receipts for the ordinary while profile.
Successful source control is distinct from its separate fault judgment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
open Core Frontend SourceInference

/-- Even before restricting the body grammar, successful while iteration can
only fall through or return. Break and continue are consumed at its boundary. -/
theorem while_control_shape {program : Program} {context finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.WhileExecutes program context evidence source environment before condition statements finalContext outcome after) :
    (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value) := by
  refine LoopStatements.while_induction
    (motive := fun _ _ _ _ _ _ _ _ outcome _ =>
      (∃ next, outcome = .fallthrough next) ∨ (∃ value, outcome = .returned value)) ?_ ?_ ?_ ?_ ?_ trace
  · intros; exact .inl ⟨_, rfl⟩
  · intros; assumption
  · intros; assumption
  · intros; exact .inl ⟨_, rfl⟩
  · intros; exact .inr ⟨_, rfl⟩

inductive ControlShape : Dynamic.ControlOutcome → Prop where
  | fallthrough (environment : Dynamic.Environment) : ControlShape (.fallthrough environment)
  | returned (value : Dynamic.Value) : ControlShape (.returned value)
  | breaking (environment : Dynamic.Environment) : ControlShape (.breaking environment)
  | continuing (environment : Dynamic.Environment) : ControlShape (.continuing environment)

theorem ControlShape.restore {outcome : Dynamic.ControlOutcome}
    (shape : ControlShape outcome) (environment : Dynamic.Environment) :
    ControlShape (Dynamic.restoreControl environment outcome) := by
  cases shape with
  | fallthrough => exact .fallthrough environment
  | returned value => exact .returned value
  | breaking => exact .breaking environment
  | continuing => exact .continuing environment

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem Tree.control_shape {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := by
  induction tree generalizing actualContext finalContext environment before after outcome with
  | body syntaxTree _ =>
    cases TypedLexicalNamedBody.syntax_control_shape syntaxTree unique executed with
    | fallthrough next _ => exact .fallthrough next
    | returned value => exact .returned value
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @breaking context scope mode id node rest expected type found form =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.breaking unique contains form head; exact .breaking environment
  | @continuing context scope mode id node rest expected type found form =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique contains form head; cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.continuing unique contains form head; exact .continuing environment
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.whileLoop unique contains form head
      rcases while_control_shape innerTrace with ⟨next, rfl⟩ | ⟨value, rfl⟩
      · exact .fallthrough environment
      · exact .returned value

theorem Tree.control_not_fault {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases tree.control_shape unique executed
open CompatibleEncoding (bind_ok)

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

open CompatibleStatementBindings (binder_projected scope_bind)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {policy : SourceCoreLoops.Policy}

/-- Real lowering supplies lexical/control trees and each actual marked
allocator receipt. `nativeLoops` supplies static native typing at the generated
loop sites; deriving those site receipts from one enclosing checker result is
a separate compiler-to-typing bridge. No child execution is required. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → CompatibleExpressionTyped.Syntax source id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionTyped.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    (nativeLoops : ∀ {fuel scope id node condition statements type conditionCode loopCode reason},
      source.lookupStatement? id = some node → node.form = .whileLoop condition statements →
      policy.lowerExpression fuel source scope condition reasonAt = .ok ⟨.bool, conditionCode⟩ →
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt false reason = .ok loopCode →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context mode statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt definitions administrative
      context scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | body syntaxTree => exact .body syntaxTree (TypedLexicalControl.tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated)

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody)

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
        exact .discard found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
          (ih closed residual sourceSignatures declarations projection generatedBody)

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      exact .block found form (innerIH closed residual sourceSignatures declarations projection generatedInner) (restIH closed residual sourceSignatures declarations projection generatedBody)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen) (elseIH closed residual sourceSignatures declarations projection generatedElse) (restIH closed residual sourceSignatures declarations projection generatedBody)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        exact .ifThen found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen) (elseIH closed residual sourceSignatures declarations projection generatedElse) (restIH closed residual sourceSignatures declarations projection generatedBody)

  | @breaking context mode id node rest expected found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .breaking found form
  | @continuing context mode id node rest expected found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .continuing found form
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      exact .whileLoop found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
        (loopIH closed residual sourceSignatures declarations projection generatedLoop)
        (nativeLoops found form generatedCondition generatedLoop)
        (restIH closed residual sourceSignatures declarations projection generatedBody)

end Solcore.SourceSemantics.CoreLowering.TypedLexicalWhile
