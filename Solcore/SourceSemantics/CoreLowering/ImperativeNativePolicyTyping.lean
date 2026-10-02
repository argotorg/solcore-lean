import Solcore.Frontend.SourceCoreLoops

/-! Native typing of the actual imperative compiler traversal. The static
admission predicate and callback laws retain the source and lexical scope.
No execution judgment or whole emitted-body typing is a field of the policy.
Concrete frontend profiles must establish these callback laws separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
open Core Frontend SourceInference
abbrev Scope := SourceCoreLoops.Scope
abbrev Admission := TypedSource → Scope → Prop

def context (scope : Scope) (administrative : Core.Context) : Core.Context :=
  SourceCoreLocalCell.coreContext scope ++ administrative

def FlowNative (definitions : DataEnvironment) (administrative : Core.Context)
    (admitted : Admission) (flow : SourceCoreLoops.FlowLowerer) : Prop :=
  ∀ fuel source scope statements type reasonAt selfReason code,
    admitted source scope → type.WellFormed definitions →
    flow fuel source scope statements type reasonAt selfReason = .ok code →
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions

/-- These are laws about the actual supplied callbacks. Admission includes the
source typing, metadata and lexical invariants needed by a concrete profile.
The match law consumes the exact recursive child callback, including its
independently admitted child sources and scopes. -/
structure PolicyLaws (definitions : DataEnvironment) (administrative : Core.Context)
    (admitted : Admission) (policy : SourceCoreLoops.Policy) : Prop where
  expression : ∀ fuel source scope id reasonAt lowered,
    admitted source scope →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    HasType (context scope administrative) lowered.expression
      (LanguageResult.resultType lowered.type) definitions
  binder : ∀ source scope binder type,
    admitted source scope → policy.lowerBinder source scope binder = .ok type →
    type.WellFormed definitions ∧ admitted source ((binder.id, type) :: scope)
  uninitialized : ∀ source scope binder payload output body code,
    admitted source scope → payload.WellFormed definitions → output.WellFormed definitions →
    HasType (context ((binder.id, payload) :: scope) administrative) body
      (LanguageResult.resultType output) definitions →
    SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id
      binder payload body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  initialized : ∀ source scope binder payload output initializer body code,
    admitted source scope → payload.WellFormed definitions → output.WellFormed definitions →
    HasType (context scope administrative) initializer (LanguageResult.resultType payload) definitions →
    HasType (context ((binder.id, payload) :: scope) administrative) body
      (LanguageResult.resultType output) definitions →
    SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id
      binder output payload initializer body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  assignment : ∀ fuel source scope site assignment operator rhs output body reasonAt code,
    admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs output body reasonAt = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  bitNot : ∀ callback source scope site assignment output body code,
    policy.assignBitNot = some callback → admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    callback source scope site assignment output body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  bitNotWithExpression : ∀ callback fuel source scope site assignment output body reasonAt code,
    policy.assignBitNotWithExpression = some callback → admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    callback policy.lowerExpression fuel source scope site assignment output body reasonAt = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  matchWith : ∀ callback flow fuel source scope id resolution type reasonAt selfReason code,
    policy.lowerMatch = some callback → FlowNative definitions administrative admitted flow →
    admitted source scope → type.WellFormed definitions →
    callback policy.lowerExpression flow fuel source scope id resolution type reasonAt selfReason = .ok code →
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {returned : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok returned) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted <;> simp_all

/-- The actual header fold preserves native typing for any typed continuation
at the resulting admitted scope. Its parent diagnostic site remains exact. -/
theorem header_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {items : List ForItemForm}
    {type : Ty} {reasonAt : ExpressionId → Word} {site : SourceCoreElaboration.ErrorSite}
    {next : Scope → Except SourceCoreBasic.Error Expr} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (continuation : ∀ finalScope body, admitted source finalScope → next finalScope = .ok body →
      HasType (context finalScope administrative) body (LocalLoop.resultType type) definitions)
    (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items type reasonAt next = .ok code) :
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions := by
  induction fuel generalizing scope items code with
  | zero =>
    cases items with
    | nil => exact continuation scope code allowed accepted
    | cons item rest => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact continuation scope code allowed accepted
    | cons item rest =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      have controlWF := LocalLoop.controlType_wellFormed wellFormed
      cases item with
      | letDecl binder initializer =>
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, accepted⟩ := bind_ok accepted
        obtain ⟨payloadWF, extended⟩ := laws.binder source scope binder payload allowed projected
        have bodyTyped := ih extended compiled
        cases initializer with
        | none => exact laws.uninitialized source scope binder payload _ body code allowed payloadWF controlWF bodyTyped accepted
        | some initializer =>
          obtain ⟨lowered, loweredAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          have same := ensure_same checked
          have initializerTyped := laws.expression fuel source scope initializer reasonAt lowered allowed loweredAccepted
          rw [← same] at initializerTyped
          exact laws.initialized source scope binder payload _ lowered.expression body code
            allowed payloadWF controlWF initializerTyped bodyTyped emitted
      | expression expression =>
        obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalSequence.discard_hasType controlWF
          (laws.expression fuel source scope expression reasonAt lowered allowed generated)
          (ih allowed compiled)
      | assignValue assignment operator rhs =>
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        exact laws.assignment fuel source scope site assignment operator rhs _ body reasonAt code
          allowed controlWF (ih allowed compiled) emitted
      | assignBitNot assignment =>
        cases selectedWith : policy.assignBitNotWithExpression with
        | some callback =>
          simp only [selectedWith] at accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.bitNotWithExpression callback fuel source scope site assignment _ body reasonAt code
            selectedWith allowed controlWF (ih allowed compiled) emitted
        | none =>
          simp only [selectedWith] at accepted
          cases selected : policy.assignBitNot with
          | none => simp [selected] at accepted
          | some callback =>
            simp only [selected] at accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            exact laws.bitNot callback source scope site assignment _ body code
              selected allowed controlWF (ih allowed compiled) emitted

/-- Every recursive statement, header, post and match child is typed by the
same actual compiler's fuel induction. Callback laws do not contain the
statement traversal or its final code as an assumed theorem. -/
theorem flow_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {statements : List StatementId}
    {type : Ty} {reasonAt : ExpressionId → Word} {tailReturns : Bool} {selfReason : Word} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
      type reasonAt tailReturns selfReason = .ok code) :
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions := by
  induction fuel generalizing source scope statements type reasonAt tailReturns selfReason code with
  | zero =>
    cases statements with
    | nil => cases accepted; exact LocalLoop.fallthrough_hasType wellFormed
    | cons id rest => cases accepted
  | succ fuel ih =>
    cases statements with
    | nil => cases accepted; exact LocalLoop.fallthrough_hasType wellFormed
    | cons id rest =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨pair, _, accepted⟩ := bind_ok accepted
      rcases pair with ⟨node, statementType⟩
      have controlWF := LocalLoop.controlType_wellFormed wellFormed
      cases form : node.form with
      | letDecl binder initializer =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨payloadWF, extended⟩ := laws.binder source scope binder payload allowed projected
        cases initializer with
        | none =>
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.uninitialized source scope binder payload _ body code allowed payloadWF controlWF
            (ih extended wellFormed compiled) emitted
        | some initializer =>
          obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          have typed := laws.expression fuel source scope initializer reasonAt lowered allowed generated
          rw [← ensure_same checked] at typed
          exact laws.initialized source scope binder payload _ lowered.expression body code
            allowed payloadWF controlWF typed (ih extended wellFormed compiled) emitted
      | assignValue assignment operator rhs =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        exact laws.assignment fuel source scope (.occurrence id.occurrence) assignment operator rhs _ body reasonAt code
          allowed controlWF (ih allowed wellFormed compiled) emitted
      | assignBitNot assignment =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        cases selectedWith : policy.assignBitNotWithExpression with
        | some callback =>
          simp only [selectedWith] at accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.bitNotWithExpression callback fuel source scope (.occurrence id.occurrence) assignment _ body reasonAt code
            selectedWith allowed controlWF (ih allowed wellFormed compiled) emitted
        | none =>
          simp only [selectedWith] at accepted
          cases selected : policy.assignBitNot with
          | none => simp [selected] at accepted
          | some callback =>
            simp only [selected] at accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            exact laws.bitNot callback source scope (.occurrence id.occurrence) assignment _ body code
              selected allowed controlWF (ih allowed wellFormed compiled) emitted
      | returnStmt expression =>
        simp only [form] at accepted
        cases expression with
        | none =>
          obtain ⟨_, resultChecked, accepted⟩ := bind_ok accepted
          obtain ⟨_, unitChecked, emitted⟩ := bind_ok accepted
          cases emitted
          have same : type = .unit := (ensure_same resultChecked).trans (ensure_same unitChecked).symm
          rw [same]
          exact LocalLoop.returned_hasType .unit
        | some expression =>
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          cases emitted
          have typed := laws.expression fuel source scope expression reasonAt lowered allowed generated
          rw [← ensure_same checked] at typed
          exact LocalLoop.returnValue_hasType wellFormed typed
      | expression expression semicolon =>
        simp only [form] at accepted
        obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
        have typed := laws.expression fuel source scope expression reasonAt lowered allowed generated
        split at accepted
        · obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          cases emitted
          rw [← ensure_same checked] at typed
          exact LocalLoop.returnValue_hasType wellFormed typed
        · split at accepted
          all_goals
            obtain ⟨_, _, accepted⟩ := bind_ok accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            cases emitted
            exact LocalSequence.discard_hasType controlWF typed (ih allowed wellFormed compiled)
      | block statements =>
        simp only [form] at accepted
        obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.sequence_hasType wellFormed
          (ih allowed wellFormed compiledBlock) (ih allowed wellFormed compiledBody)
      | ifThen condition thenBody elseBody =>
        simp only [form] at accepted
        obtain ⟨conditionCode, generated, accepted⟩ := bind_ok accepted
        obtain ⟨_, checked, accepted⟩ := bind_ok accepted
        obtain ⟨thenCode, compiledThen, accepted⟩ := bind_ok accepted
        have conditionTyped := laws.expression fuel source scope condition reasonAt conditionCode allowed generated
        rw [← ensure_same checked] at conditionTyped
        cases elseBody with
        | none =>
          obtain ⟨elseCode, compiledElse, accepted⟩ := bind_ok accepted
          cases compiledElse
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          exact LocalLoop.sequence_hasType wellFormed
            (LocalLoop.conditional_hasType wellFormed conditionTyped (ih allowed wellFormed compiledThen)
              (LocalLoop.fallthrough_hasType wellFormed))
            (ih allowed wellFormed compiledBody)
        | some statements =>
          obtain ⟨elseCode, compiledElse, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          exact LocalLoop.sequence_hasType wellFormed
            (LocalLoop.conditional_hasType wellFormed conditionTyped (ih allowed wellFormed compiledThen)
              (ih allowed wellFormed compiledElse))
            (ih allowed wellFormed compiledBody)
      | whileLoop condition statements =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨conditionCode, generated, accepted⟩ := bind_ok accepted
        obtain ⟨_, checked, accepted⟩ := bind_ok accepted
        obtain ⟨loopCode, compiledLoop, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        have conditionTyped := laws.expression fuel source scope condition reasonAt conditionCode allowed generated
        rw [← ensure_same checked] at conditionTyped
        exact LocalLoop.sequence_hasType wellFormed
          (LocalLoop.whileLoop_hasType selfReason wellFormed conditionTyped (ih allowed wellFormed compiledLoop))
          (ih allowed wellFormed compiledBody)
      | forLoop initializer condition post statements =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨loopCode, compiledLoop, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        apply LocalLoop.sequence_hasType wellFormed ?_ (ih allowed wellFormed compiledBody)
        apply header_native laws allowed wellFormed ?_ compiledLoop
        intro loopScope loopBody loopAllowed continued
        obtain ⟨conditionCode, generated, continued⟩ := bind_ok continued
        obtain ⟨_, checked, continued⟩ := bind_ok continued
        obtain ⟨bodyCode, bodyAccepted, continued⟩ := bind_ok continued
        obtain ⟨postCode, postAccepted, emitted⟩ := bind_ok continued
        cases emitted
        have conditionTyped := laws.expression fuel source loopScope condition reasonAt conditionCode loopAllowed generated
        rw [← ensure_same checked] at conditionTyped
        apply LocalLoop.iterate_hasType selfReason wellFormed conditionTyped (ih loopAllowed wellFormed bodyAccepted)
        apply header_native laws loopAllowed wellFormed ?_ postAccepted
        intro postScope postBody _ compiledPost
        cases compiledPost
        exact LocalLoop.fallthrough_hasType wellFormed
      | matchWith resolution =>
        simp only [form] at accepted
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some callback =>
          simp only [selected] at accepted
          obtain ⟨matched, compiledMatch, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          apply LocalLoop.sequence_hasType wellFormed ?_ (ih allowed wellFormed compiledBody)
          apply laws.matchWith callback _ fuel source scope id resolution type reasonAt selfReason matched
            selected ?_ allowed wellFormed compiledMatch
          intro childFuel childSource childScope childStatements childType childReason childSelf childCode childAllowed childWF childAccepted
          exact ih childAllowed childWF childAccepted
      | breakStmt =>
        simp only [form] at accepted
        obtain ⟨_, _, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.breaking_hasType wellFormed
      | continueStmt =>
        simp only [form] at accepted
        obtain ⟨_, _, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.continuing_hasType wellFormed

/-- Finish and escaped-loop handling are the actual compiler wrappers. The
fallback is typed for both Unit and non-Unit results without weakening fuel
exhaustion into a completed source execution. -/
theorem body_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {statements : List StatementId}
    {type : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      type reasonAt fellThrough escaped = .ok code) :
    HasType (context scope administrative) code (LanguageResult.resultType type) definitions := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := bind_ok accepted
  cases emitted
  apply LocalControl.finish_hasType wellFormed
    (LocalLoop.toControl_hasType escaped wellFormed (flow_native laws allowed wellFormed generated))
  split
  · rename_i same
    simpa only [same] using (LanguageResult.success_hasType (HasType.unit
      (context := context scope administrative) (definitions := definitions)))
  · exact LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
