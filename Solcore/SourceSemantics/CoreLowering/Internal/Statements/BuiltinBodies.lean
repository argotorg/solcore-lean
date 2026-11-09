import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedNamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls

/-!
# Builtin bodies

Lexical statements, body certificates and meaning, and named calls of builtin bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
/-! The generic statement interface is instantiated by the complete recursive
builtin/data/control/index grammar. Production contextual success extracts
static certificates, and the concrete expression theorem discharges every child
meaning obligation at the actual lexical context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericLexicalStatements
open Core Frontend SourceInference
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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Arbitrarily mixed ordinary lets are extracted from the real
compiler, including each actual marker/snapshot allocator receipt. -/
theorem tree_of_flow_with_residual (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context mode statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code with
  | nil allowed =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    cases accepted
    exact .nil allowed
  | @returnUnit context mode id node rest found form sourceType =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
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
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .returnUnit rest found form
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed syntaxValue =>
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
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .returnValue rest found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      exact .tail found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (extractExpressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated)
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
        exact .discard found form notTail expressionFound (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated)
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
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen) (elseIH closed residual sourceSignatures declarations projection generatedElse) (restIH closed residual sourceSignatures declarations projection generatedBody)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
          (thenIH closed residual sourceSignatures declarations projection generatedThen) (elseIH closed residual sourceSignatures declarations projection generatedElse) (restIH closed residual sourceSignatures declarations projection generatedBody)

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      exact .terminalBlock exactUnique found form
        (innerIH closed residual sourceSignatures declarations projection generatedInner) stops
        (IssuedSuffix.of_accepted generatedSuffix)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
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
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      exact .terminalIf exactUnique found form conditionFound conditionType
        (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition)
        (thenIH closed residual sourceSignatures declarations projection generatedThen)
        (elseIH closed residual sourceSignatures declarations projection generatedElse)
        thenStops elseStops (IssuedSuffix.of_accepted generatedSuffix)

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context mode statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  exact tree_of_flow_with_residual false (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (extractExpressions := extractExpressions) (context := context)
    (scope := scope) (mode := mode) (statements := statements) (expected := expected) (syntaxTree := syntaxTree)
    (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (fuel := fuel) (type := type) (code := code) (selfReason := selfReason) (projection := projection)
    (accepted := accepted)

/-- The complete production body wrapper keeps the extracted binding spine. -/
theorem tree_of_body_with_residual (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context true statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError values source certificates
        context scope true statements expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy extractExpressions syntaxTree closed residual sourceSignatures declarations projection generated⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context true statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError values source certificates
        context scope true statements expected type flow := by
  exact tree_of_body_with_residual false (readPolicy := readPolicy) (binderPolicy := binderPolicy)
    (allocationPolicy := allocationPolicy) (extractExpressions := extractExpressions) (context := context)
    (scope := scope) (statements := statements) (expected := expected) (syntaxTree := syntaxTree) (closed := closed)
    (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations) (fuel := fuel)
    (type := type) (code := code) (fellThrough := fellThrough) (escaped := escaped) (projection := projection)
    (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.GenericLexicalStatements

namespace Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Syntax (source : TypedSource) := GenericLexicalStatements.Syntax source (CompatibleExpressionBuiltins.Syntax source)
abbrev Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  GenericLexicalStatements.Tree layouts owner active frame globals onError values source
    (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope} {context : SourceSemantics.Context}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation (some native) parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source context true statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt
        context scope true statements expected type flow := by
  apply GenericLexicalStatements.tree_of_body readStatement ?_ sourceCells ?_ syntaxTree closed residual sourceSignatures declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro sourceContext contextClosed contextResidual contextSignatures currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionBuiltins.tree_of_contextual ordinary unique contextClosed contextResidual currentDeclarations contextSignatures
      syntaxValue found typed readExpression lowerRead leafLowerer generated


variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include definitions registered extension faithful functionLeaves functionTypes uninitialized missing in
/-- Concrete recursive builtin trees close every expression position, including
let initializers and conditions after lexical extension. No child execution or
universal expression meaning is a premise of this public consumer. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) :
    TypedLexicalControl.Preserves functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped trace
  exact GenericLexicalStatements.Tree.preserves functions definitions registered program evidence
    (fun context contextValid => CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
      program evidence contextValid unique uninitialized missing)
    tree valid unique environments heaps locals agrees actualTyped reference read unmapped trace

include definitions registered extension faithful functionLeaves functionTypes uninitialized missing in
/-- Every finite native flow completion constructs independent source
execution. The real typed captures and frame/metadata protection are retained
while the recursive builtin expression theorem discharges all child reflection. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError readFuel values source solved reasonAt
      context scope mode statements expected type code) :
    TypedLexicalControl.Reflects functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped completed
  exact GenericLexicalStatements.Tree.reflects functions definitions registered program evidence
    (fun context contextValid => CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
      program evidence contextValid uninitialized missing)
    tree valid environments heaps locals agrees actualTyped reference read unmapped completed

end Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyCertificates
/-! Static receipts for the ordinary lexical named-body fragment with recursive builtin expressions. A receipt
retains the actual production traversal equation and its extracted statement
tree at its initial source context. It contains no body execution or semantic induction
hypothesis. Context/evidence validity remains a separate static obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
open Core Frontend SourceInference

structure Certificate (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope true
    statements expected type flow

/-- Static extraction can also retain an already extracted production flow.
The actual body action and finish equation remain required; there is no
execution field or semantic hypothesis in this factory. -/
theorem of_tree
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (emitted : code = CompatibleStatements.finish type flow fellThrough escaped)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values
      source solved reasonAt context scope true statements expected type flow) :
    Nonempty (Certificate layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :=
  ⟨⟨accepted, projection, syntaxTree, flow, emitted, tree⟩⟩

/-- Extract the body tree from the actual contextual compiler. Every remaining
premise concerns source syntax, typing, context, or a production policy field. -/
theorem of_contextual
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {policy : SourceCoreLoops.Policy}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation (some native) parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code) :
    Nonempty (Certificate layouts owner active frame globals onError readFuel values source context compilation.solvedRequirements reasonAt scope
      statements expected type policy fuel fellThrough escaped code) := by
  obtain ⟨flow, emitted, tree⟩ := BuiltinLexicalStatements.tree_of_contextual_body ordinary unique closed residual sourceSignatures
    declarations readExpression lowerRead leafLowerer readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection accepted
  exact ⟨⟨accepted, projection, syntaxTree, flow, emitted, tree⟩⟩

/-- Instantiate the generic named compiler decomposition with the concrete
lexical builtin-statement tree, at the actual scope after parameter installation.
All context/evidence/ordinary obligations are explicit static hypotheses. -/
theorem compilation_of_accepted
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {allocationGlobals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {plan : SourceSpecializationWorklist.Plan}
    {globals : List SourceCoreCalls.Signature} {locals : SourceCoreLocalPolymorphism.Catalog}
    {native : SourceCoreGeneralFunctions.CallableContext}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {named : SourceCoreGeneralFunctions.Function}
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {readFuel fuel : Nat} {values : SourceCoreCompatibleValues.Context} {code : Expr}
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (parentReceipt : SourceCoreStageCodebook.prepareContexts program plan
      (locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : diagnostics.base.find? named.signature.key = some own)
    (ordinary : CompatibleExpressionBuiltins.Ordinary function.source locals named.signature.key)
    (unique : NodeOccurrencesUnique function.source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readExpression : (representation.atContext named.signature.key []).expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : (representation.atContext named.signature.key []).expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : (representation.atContext named.signature.key []).expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (lowerExpression : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression program (representation.atContext named.signature.key [])
        signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native) none none)
    (representationBinder : (representation.atContext named.signature.key []).expressions.lowerBinder =
      SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).lowerBinder =
      SourceCoreGeneralFunctions.contextualBinder (representation.atContext named.signature.key []) locals named.signature.key [])
    (sourceCells : (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key []) program signatures locals parents
      own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native)).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (allocator : (representation.atContext named.signature.key []).expressions.sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)))
    (syntaxTree : BuiltinLexicalStatements.Syntax function.source context true function.body function.resultType)
    (projection : values.checked.catalog.project function.resultType = .ok named.signature.resultType)
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation program representation signatures plan globals
      diagnostics locals (some native) fuel named = .ok code) :
    Nonempty (NamedCompilationReceipt.Receipt program representation signatures plan globals diagnostics locals (some native) parents own
      named function.body fuel
      (SourceCoreCallableIndexedAllocationFrames.allocator frame allocationGlobals (layouts.allocatorAt owner active onError)) (fun body => Nonempty (Certificate layouts owner active frame allocationGlobals onError readFuel values function.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType
        named.signature.resultType (CompatibleNamedBody.bodyPolicy (representation.atContext named.signature.key [])
          program signatures locals parents own.assignments diagnostics (CompatibleNamedBody.bodyContext plan globals named) (some native))
        fuel own.fellThroughReason own.table.escapedReason body)) code) := by
  apply NamedCompilationReceipt.of_accepted (agreement.source ▸ agreement.roots) parentReceipt diagnosticReceipt allocator ?_ accepted
  intro body lowered
  change SourceCoreLoops.lowerStatementsWithPolicy _ _ _ _ _ _ _ _ _ = .ok body at lowered
  rw [← agreement.source] at lowered
  exact of_contextual ordinary unique closed residual declarations sourceSignatures readExpression lowerRead leafLowerer
    readStatement representationBinder lowerBinder sourceCells lowerExpression syntaxTree projection lowered

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinBodySemanticReceipt
/-! Static evidence consumed by the concrete builtin body semantics.
Compiler acceptance is retained by the separate production certificate; the
semantic receipt keeps the exact finished code and independent source syntax.
It contains no body execution or child meaning field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
open Core Frontend SourceInference

structure SemanticReceipt (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (fellThrough escaped : Word) (code : Expr) where private mk ::
  projection : values.checked.catalog.project expected = .ok type
  syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope true
    statements expected type flow

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
  {fellThrough escaped : Word} {code flow : Expr}

/-- Every field is independent static evidence for this exact source and code.
This factory does not assert a production compiler equation. -/
def SemanticReceipt.of_tree
    (projection : values.checked.catalog.project expected = .ok type)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (emitted : code = CompatibleStatements.finish type flow fellThrough escaped)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values
      source solved reasonAt context scope true statements expected type flow) :
    SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type fellThrough escaped code :=
  ⟨projection, syntaxTree, flow, emitted, tree⟩

/-- The original production receipt supplies all semantic evidence while
continuing to retain its own accepted compiler equation. -/
def Certificate.semantic {policy : SourceCoreLoops.Policy} {fuel : Nat}
    (certificate : Certificate layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type fellThrough escaped code :=
  SemanticReceipt.of_tree certificate.projection certificate.syntaxTree certificate.emitted certificate.tree

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyMeaning
/-! The concrete recursive builtin statement tree supplies the named body
beneath its actual finish helper. Raw source return typing fixes true-mode
fallthrough; lexical allocations and stopping contexts remain observable.
Neither source execution nor a universal body meaning is stored in a receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control body_result)
open GenericLexicalStatements (true_fallthrough_unit control_not_fault)

private theorem finish_rename (type : Ty) (flow : Expr) (fellThrough escaped : Word) (ξ : Renaming) :
    (CompatibleStatements.finish type flow fellThrough escaped).rename ξ = CompatibleStatements.finish type (flow.rename ξ) fellThrough escaped := by
  unfold CompatibleStatements.finish
  split <;> simp [LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem finish_input {environment : Environment} {before after : Store} {type : Ty}
    {flow : Expr} {fellThrough escaped : Word} {result : Value}
    (evaluated : Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after) :
    ∃ value middle, Evaluates environment before flow value middle := by
  cases evaluated with
  | caseLeft control branch | caseRight control branch =>
    cases control with
    | caseLeft input branch | caseRight input branch => exact ⟨_, _, input⟩

private theorem finish_from_flow
    {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {source : TypedSource} {context actualContext finalContext : SourceSemantics.Context}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {sourceBefore sourceAfter : Dynamic.Heap}
    {statements : List StatementId} {environment : Environment} {before after : Store}
    {expected : TypeSystem.Ty} {type : Ty} {outcome : Dynamic.ControlOutcome} {flow : Expr} {value : Value}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (unique : NodeOccurrencesUnique source)
    (trace : Executes true program actualContext evidence source sourceEnvironment sourceBefore statements finalContext outcome sourceAfter)
    (projection : values.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word)
    (represented : TypedScopedStatements.FlowRep (registry := registry) functions mapping world faults expected type outcome value)
    (evaluated : Evaluates environment before flow value after) :
    ∃ result, Evaluates environment before (CompatibleStatements.finish type flow fellThrough escaped) result after ∧
      CompatibleStatements.BodyRep (registry := registry) functions mapping world faults expected type outcome result := by
  cases represented with
  | fallthrough nextEnvironment =>
    have raw := true_fallthrough_unit syntaxTree unique trace
    subst expected
    have native : type = .unit := by
      change Except.ok (.unit : Ty) = .ok type at projection
      exact Except.ok.inj projection.symm
    subst type
    exact ⟨_, LocalControl.finish_fallthrough .unit (LocalLoop.toControl_normal _ escaped evaluated)
      (by simpa [LanguageResult.success, Expr.weakenAt] using
        (show Evaluates (.unit :: .inLeft .unit .unit :: environment) after (.inRight .word .unit) (.inRight .word .unit) after from .inRight .unit)),
      .fallthrough nextEnvironment⟩
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned _ (LocalLoop.toControl_normal _ escaped evaluated), .returned payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated), .fault matched⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (program : Program)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem SemanticReceipt.preserves [FunctionCalls.FaultTokens faults]
    (certificate : SemanticReceipt layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves functions definitions registered extension faithful functionLeaves functionTypes program function.evidence uninitialized missing
      unique contextValid environments heaps locals agrees actualTyped reference read unmapped sourceTrace
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique sourceTrace
    certificate.projection fellThrough escaped represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, finish_rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, body_result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩⟩

include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem SemanticReceipt.reflects [FunctionCalls.FaultTokens faults]
    (certificate : SemanticReceipt layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  rw [certificate.emitted, finish_rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := finish_input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects functions definitions registered extension faithful functionLeaves functionTypes program function.evidence uninitialized missing
      contextValid environments heaps locals agrees actualTyped reference read unmapped flowEval
  obtain ⟨result, completed, related⟩ := finish_from_flow functions certificate.syntaxTree unique trace
    certificate.projection fellThrough escaped represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (control_not_fault certificate.syntaxTree unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩⟩


/- The accepted compiler certificate keeps the original public interface. -/
include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.preserves [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  exact certificate.semantic.preserves functions extension definitions registered program contextValid unique
    uninitialized missing faithful functionLeaves functionTypes environments heaps locals agrees actualTyped reference read unmapped trace

/- The accepted compiler certificate keeps the original completed reflection interface. -/
include definitions registered extension faithful functionLeaves functionTypes contextValid unique uninitialized missing in
theorem Certificate.reflects [FunctionCalls.FaultTokens faults]
    (certificate : Certificate layouts owner active frameLayout globals onError readFuel values function.source context solved reasonAt scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  exact certificate.semantic.reflects functions extension definitions registered program contextValid unique
    uninitialized missing faithful functionLeaves functionTypes environments heaps locals agrees actualTyped reference read unmapped evaluated

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
/-! Ordinary named calls retain their actual source definition, installed
closure and indexed frame history. Concrete recursive builtin argument and
lexical body trees discharge the child and body semantics. Parameter allocation
and the finish helper use their real compiler receipts; no semantic field is
stored in the static body certificate. -/
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Frontend SourceInference
private theorem definition_unique {definitions : List FunctionDefinition}
    (unique : (definitions.map (fun definition => definition.body.owner)).Nodup)
    {left right : FunctionDefinition} (leftMem : left ∈ definitions) (rightMem : right ∈ definitions)
    (owner : left.body.owner = right.body.owner) : left = right := by
  induction definitions with
  | nil => cases leftMem
  | cons head tail ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    simp only [List.mem_cons] at leftMem rightMem
    rcases leftMem with rfl | leftMem
    · rcases rightMem with rfl | rightMem
      · rfl
      · exact False.elim (absent (List.mem_map.mpr ⟨right, rightMem, owner.symm⟩))
    · rcases rightMem with rfl | rightMem
      · exact False.elim (absent (List.mem_map.mpr ⟨left, leftMem, owner⟩))
      · exact ih unique leftMem rightMem

theorem instantiation_unique {program : Program} {instantiation : DeclarationInstantiation}
    {left right : Dynamic.BodyInstance}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (first : Dynamic.FunctionInstantiates program instantiation left)
    (second : Dynamic.FunctionInstantiates program instantiation right) : left = right := by
  cases first with
  | @intro signature definition _ signatureMem definitionMem declaration owner valid source result context =>
    cases second with
    | @intro otherSignature otherDefinition _ otherSignatureMem otherDefinitionMem otherDeclaration otherOwner otherValid otherSource otherResult otherContext =>
      have same : definition = otherDefinition := definition_unique unique definitionMem otherDefinitionMem
        ((owner.trans declaration.symm).trans (otherOwner.trans otherDeclaration.symm).symm)
      cases same
      cases left
      cases right
      simp_all

theorem instantiation_unique_of_wellFormed {program : Program} {instantiation : DeclarationInstantiation}
    {left right : Dynamic.BodyInstance} (wellFormed : ProgramWellFormed program)
    (first : Dynamic.FunctionInstantiates program instantiation left)
    (second : Dynamic.FunctionInstantiates program instantiation right) : left = right :=
  instantiation_unique wellFormed.function_ids first second

/-- A real independent global dispatch uses the exact catalog body in its
source frame. Owner uniqueness and the represented argument arity rule out
missing/arity faults; neither Core code nor a specialization shape selects it. -/
theorem source_dispatch {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (called : FunctionCallBody.Outcome program context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    NamedCalls.BodyOutcome program body function.evidence before arguments outcome after := by
  cases called with
  | value evaluated =>
    cases evaluated with
    | global actual invocation covers invoked =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact .value invoked
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ signatureMem declaration.symm)
    | globalBodyMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ definitionMem (owner.trans declaration.symm))
    | globalArity actual mismatch =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | globalBody actual invocation failed =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact .fault failed

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls.Parameters
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
  (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
theorem preserves_with
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (continuation : ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached⟩ := continuation trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

theorem reflects_with
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (continuation : ∀ {value : Value} {finalStore : Store},
      Evaluates entry.actualBody entry.store (body.rename entry.embedding) value finalStore →
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    continuation (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem preserves [FunctionCalls.FaultTokens faults]
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  exact preserves_with functions program entry
    (fun trace => certificate.preserves functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped trace) trace

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem reflects [FunctionCalls.FaultTokens faults]
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  exact reflects_with functions program entry
    (fun evaluated => certificate.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped evaluated) evaluated

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls.Parameters

namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open NamedCalls (withFrame_rename)

private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped in
/-- Shared native frame envelope. Its parameter continuation is supplied only by the concrete legacy or runtime body proof. -/
theorem hook_preserves_with_spine
    (Trace : Dynamic.Environment → Dynamic.Heap → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop)
    (prefixMeaning : ∀ (origin : Word) (index : Int) (metadata : MetadataState),
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin →
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
      ∀ {prefixContext : Core.Context} {prefixActual : Environment} {embedding : Renaming}
      (entry : TypedMixedNamedParameters.Entry prepared.layout.frame allocationGlobals location (.state index)
        values functions registry function context bindings arguments before
        (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative prefixContext prefixActual embedding parameterCode body)
      (added : Environment), added.length = bindings.length →
      entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical →
      ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      Trace entry.environment entry.heap outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates prefixActual (store.set location (encode prepared.layout.frame (.state index)))
          (parameterCode.rename embedding) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld function.resultType output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping (store.set location (encode prepared.layout.frame (.state index))) finalMap finalStore ∧
        Dynamic.HeapMetadataExtend before after ∧
        TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
          (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : Trace environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry, added, prefixLength, spine⟩ := TypedMixedNamedParameters.entry_of_accepted_with_spine functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    prefixMeaning origin index metadata owned history entry added prefixLength spine trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    renamed.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, by simpa only [sameEnvironment, sameHeap] using reached⟩


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped in
/-- The legacy continuation forgets the extra actual history and spine only. -/
theorem hook_preserves_with
    (prefixMeaning : ∀ {next : NativeFrame} {parameterStore : Store}
      {prefixContext : Core.Context} {prefixActual : Environment} {embedding : Renaming}
      (entry : TypedMixedNamedParameters.Entry prepared.layout.frame allocationGlobals location next
        values functions registry function context bindings arguments before parameterStore mapping world
        administrative prefixContext prefixActual embedding parameterCode body)
      {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates prefixActual parameterStore (parameterCode.rename embedding) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld function.resultType output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping parameterStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
          (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  exact hook_preserves_with_spine (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (FunctionCallBody.Trace program function context)
    (fun _ _ _ _ _ {_ _ _} entry _ _ _ {_ _} trace => prefixMeaning entry trace) allocated trace


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
theorem hook_preserves [FunctionCalls.FaultTokens faults] {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  exact hook_preserves_with (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (fun {_ _ _ _ _} entry {_ _} trace => BuiltinNamedCalls.Parameters.preserves functions extension definitions registered program
      contextValid unique uninitialized missing faithful functionLeaves functionTypes entry certificate trace) allocated trace

include registered heaps unmapped typed caller snapshots in
/-- Restore the exact caller from one reflected parameter-prefix result. The
caller supplies the original split, so a sized consumer keeps its own native child. -/
theorem hook_reflects_from_prefix {value : Value} {finalStore bodyStore : Store}
    {origin : Word} {index : Int} {metadata : MetadataState}
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata))
    (finalEq : finalStore = bodyStore.set location (encode prepared.layout.frame current))
    (prefixMeaning :
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before
        (store.set location (encode prepared.layout.frame (.state index))) →
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location (.state index) (.named origin)
        (store.set location (encode prepared.layout.frame (.state index))) →
    ∃ environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping (store.set location (encode prepared.layout.frame (.state index))) finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadataExtend, reached⟩ := prefixMeaning installedHeaps installedCaller
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, environment, bound, outcome, after, finalMap, finalWorld, owned, history,
    allocated, trace, related, restoredHeaps, maps, worlds, restoredFrame, metadataExtend,
    restoredCaller, snapshots.transport restoredFrame, reached⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace from the installed call context with its actual lexical stopping context. -/
theorem hook_reflects [FunctionCalls.FaultTokens faults] {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  apply hook_reflects_from_prefix (prepared := prepared) (functions := functions) (program := program)
    (registered := registered) (heaps := heaps) (unmapped := unmapped)
    (typed := typed) (caller := caller) (snapshots := snapshots) owned history finalEq
  intro installedHeaps installedCaller
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    BuiltinNamedCalls.Parameters.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry certificate bodyEvaluation
  exact ⟨entry.environment, entry.heap, outcome, after, finalMap, finalWorld,
    entry.allocation, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩


end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
open CallableIndexedHistory CallableIndexedParameterCertificates
open SourceCoreCallableIndexedFrames

open NamedCalls.Arguments (call_rename arguments_complete body_complete expression)
abbrev Trace := NamedCalls.Arguments.Trace
abbrev Emission := NamedCalls.Arguments.Emission

abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-- Static body compilation and independent declaration attribution. There
is no source execution, native execution or body meaning field. -/
structure Body {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  closed : named.specialized.assumptions = []
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame globals onError readFuel values
    function.source context solved reasonAt (bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    function.body function.resultType output policy fuel fellThrough escaped body
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)

private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

private theorem arguments_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {bindings : List Binding}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads) :
    RuntimeValueHasType world (DataPatternValues.packValues payloads)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) definitions := by
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => simpa [DataPatternValues.packValues, SourceCoreCompatibleCatalog.packTypes] using model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Real installed environments, code and frame state. These observational
facts grant no source declaration or body semantics; those are in `Body`. -/
structure Installed {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {program : Program} (body : Body prepared values ambient.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)
    (before : Dynamic.Heap) (store : Store) (callerEnvironment : Environment) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before body.function.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[body.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType body.named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure body.named.signature.parameterType (LanguageResult.resultType body.named.signature.resultType)
      (body.code.rename embedding.lift) captured))

/-- Argument effects preserve the exact installed closure and both protected
administrative histories. Captured environment typing is weakened along the
actual world extension, including all non-source slots. -/
def Installed.extend {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {program : Program}
    {body : Body prepared values ambient.definitions program} {registry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed functions body registry futureMapping futureWorld after futureStore callerEnvironment := by
  have frameBound := (List.getElem?_eq_some_iff.mp installed.caller.read).1
  have globalBound := (List.getElem?_eq_some_iff.mp installed.globalRead).1
  have frame := preserved installed.frameLocation installed.unmapped frameBound
  have global := preserved installed.globalLocation installed.globalUnmapped globalBound
  exact { installed with
    environments := installed.environments.extend maps worlds
    locals := installed.locals.mono metadata
    captureTyped := installed.captureTyped.weaken worlds
    unmapped := frame.1
    frameTyped := worlds.lookup installed.frameTyped
    caller := ⟨frame.2.trans installed.caller.read, installed.caller.history⟩
    snapshots := installed.snapshots.transport preserved
    globalUnmapped := global.1
    globalRead := global.2.trans installed.globalRead }

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} (body : Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include extension uninitialized missing faithful functionLeaves functionTypes in
/-- The concrete parameter/body certificates close this body invocation after
the real argument effects. The only source execution premise is the particular
independent invocation being preserved. -/
theorem body_preserves [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]; exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := body.frame.trace_of_body body.extended arity executed
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluation, result, finalHeaps,
    maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    hook_preserves prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing faithful functionLeaves functionTypes body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots allocated trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds,
    preserved, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Independent global application dispatches to the exact retained source
body under actual program owner uniqueness. The concrete builtin body closes
its semantics; an exact-body source trace is not a premise of this consumer. -/
theorem body_dispatch_preserves [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed program)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (called : FunctionCallBody.Outcome program callerContext callerEvidence body.function.evidence before
      (.global ⟨body.instantiation, body.function.evidence⟩) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]
    exact represented.length.1
  exact body_preserves functions extension body uninitialized missing faithful functionLeaves functionTypes
    installed represented heaps (source_dispatch wellFormed.function_ids body.frame arity called)

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Completed actual body execution constructs parameter allocation and the
independent invocation from the concrete lexical tree, with frame restoration. -/
theorem body_reflects [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
      (body.code.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace, result,
    finalHeaps, maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    hook_reflects prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing faithful functionLeaves functionTypes body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots executed
  exact ⟨outcome, after, finalMap, finalWorld, body.frame.body_of_trace body.extended allocated trace,
    result, finalHeaps, maps, worlds, preserved, metadata, current, snapshots⟩

variable {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleExpressionLiterals.ContextValid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd)
  (packedType : body.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Concrete recursive builtin argument trees close all child meaning. Arguments are
evaluated before the global read; their first fault skips the body. The body
uses its actual static parameter/lexical certificates at the intervening heap. -/
theorem preserves [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
    simpa only [body.resultType] using
      (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (sourceType := body.function.resultType) (type := body.output) matched)
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments body.bindings represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ := body_preserves functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType body.named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Every finite native call completion reconstructs its ordered source
argument trace and concrete independent named-body invocation. Neither child
evaluations nor a universal body preservation hypothesis are supplied. -/
theorem reflects [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
        before ids body.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentValue, middleStore, argumentEvaluation⟩ := arguments_complete completed
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
        (internalReason := reason) (packedType.symm ▸ argumentEvaluation)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      refine ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, ?_, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
      simpa only [body.resultType] using
        (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
          (sourceType := body.function.resultType) (type := body.output) matched)
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments body.bindings represented
      have bodyEvaluation := body_complete argumentEvaluation installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩ := body_reflects functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Actual compiler success, independent source attribution and concrete
argument/body certificates close reflection at the emitted expression itself. -/
theorem accepted_reflects [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  rw [emitted, call_rename, ← located] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    reflects functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed trace,
    result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Preservation starts with this exact independently instantiated source body
and ordered argument trace. The actual accepted emitted expression is evaluated,
including argument faults and lexical body faults with their preceding writes. -/
theorem accepted_preserves [FunctionCalls.FaultTokens faults] {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    preserves functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped unique execution
  have completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore := by
    rw [emitted, call_rename, ← located]; exact evaluation
  exact ⟨value, finalStore, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed execution,
    completed, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
end
