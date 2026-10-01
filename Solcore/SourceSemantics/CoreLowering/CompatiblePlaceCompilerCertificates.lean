import Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping

/-! Actual compatible place lowering receipts. These follow production Except
branches and reuse the common child/key certificate relations. The compiler is
not duplicated, and no source or native evaluation is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open DataPlaceCertificates CompatibleMixedRoute

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

inductive Generated (compilation : SourceCoreCompatibleDataPlaces.Context) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Ty) (next : Expr) (reasonAt : ExpressionId → Word)
    (invalidProjection invalidOperand : Word) (missing : TypeSystem.Ty → Word) : Expr → Prop where
  | intro (route : Route) (prepared : Prepared) (index : Nat)
      (keys : List SourceCoreBasic.LoweredExpr) (value : Expr)
      (described : describe compilation signatures source site assignment = .ok route)
      (lookup : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType))
      (preparedBy : prepare compilation fuel route invalidProjection missing = .ok prepared)
      (keysGenerated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys keys)
      (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer)
      (rhsGenerated : RhsGenerated expression fuel source scope reasonAt route.leafType rhs value) :
      Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
        reasonAt invalidProjection invalidOperand missing
        (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value next outputType
          (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)

/-- The receipt follows actual successful compiler branches. It does not
replace or reinterpret the executable place compiler. -/
theorem generated_of_lower {compilation : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word} {lowered : Expr}
    (accepted : lower compilation signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing lowered := by
  unfold lower at accepted
  obtain ⟨route, described, accepted⟩ := bind_ok accepted
  cases lookup : SourceCoreLocalCell.lookup? scope assignment.target.root with
  | none => simp [lookup, throw, bind, Except.bind] at accepted
  | some pair =>
    obtain ⟨index, storedType⟩ := pair
    simp only [lookup, pure, Except.pure, bind, Except.bind] at accepted
    cases typed : SourceCoreBasic.ensureType site route.rootType storedType with
    | error error => simp [typed] at accepted
    | ok checkedUnit =>
      cases checkedUnit
      have types := ensureType_ok typed
      subst storedType
      simp only [typed] at accepted
      obtain ⟨prepared, preparedBy, accepted⟩ := bind_ok accepted
      obtain ⟨keys, keysCompiled, accepted⟩ := bind_ok accepted
      have keyCertificate := keys_generated keysCompiled
      have finish (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer)
          (completed : (show Except SourceCoreBasic.Error Expr from match rhs with
            | none => .ok (execute prepared (.var index) (SourceCoreCalls.packArguments keys)
                (LanguageResult.success .unit) next outputType
                (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)
            | some id => do
                let value ← expression fuel source scope id reasonAt
                SourceCoreBasic.ensureType site route.leafType value.type
                pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value.expression next outputType
                  (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)) = .ok lowered) :
          Generated compilation signatures expression fuel source scope site assignment operator rhs outputType next
            reasonAt invalidProjection invalidOperand missing lowered := by
        cases rhs with
        | none =>
          simp only [Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid .absent
        | some id =>
          obtain ⟨value, valueCompiled, completed⟩ := bind_ok completed
          obtain ⟨checkedUnit, typeChecked, completed⟩ := bind_ok completed
          cases checkedUnit
          simp only [pure, Except.pure, Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid
            (.present valueCompiled (ensureType_ok typeChecked))
      by_cases same : operator = .equal
      · cases rhs with
        | none =>
          by_cases word : route.leafType = .word
          · apply finish (.inr (.inl word)); simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
          · by_cases integer : route.leafType = Core.Ty.integer
            · apply finish (.inr (.inr integer)); simpa [same, integer, pure, Except.pure, bind, Except.bind] using accepted
            · simp [same, word, integer, throw] at accepted
        | some id =>
          apply finish (.inl ⟨same, rfl⟩)
          simpa [same, pure, Except.pure, bind, Except.bind] using accepted
      · by_cases word : route.leafType = .word
        · apply finish (.inr (.inl word)); cases rhs <;> simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
        · by_cases integer : route.leafType = Core.Ty.integer
          · apply finish (.inr (.inr integer)); cases rhs <;> simpa [same, integer, pure, Except.pure, bind, Except.bind] using accepted
          · simp [same, word, integer, throw] at accepted


theorem PreparedPath.key_ids {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) :
    keys.map Prod.fst = DataPlaceKeyOrder.sourceKeys projections := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih => exact ih
  | index _ _ _ ih => exact congrArg (List.cons _) ih

theorem PreparedPath.steps_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

/-- Ordered child certificates come from the actual mapM receipt and path
occurrences, so repeated index occurrences remain repeated evaluations. -/
theorem tree_of_keys {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {expression : ExpressionLowerer} {fuel : Nat} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes ∧
      keys.map Prod.snd = codes.map (·.type) := by
  have collect : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail ih => exact ⟨.cons (extract _ _ head.1) ih.1, by simp only [List.map_cons, head.2, ih.2]⟩
  have receipts := collect generated
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [PreparedPath.key_ids path] at tree
  exact ⟨types, tree, receipts.2⟩

/-- The checked wrapper retains the exact accepted production lowering. Its
public typed field refers to the caller's actual definitions and context. -/
theorem lower_of_lowerChecked {compilation : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures}
    {expression : ExpressionLowerer} {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word} {definitions : DataEnvironment} {environment : Core.Context}
    {certified : Certified definitions environment outputType}
    (accepted : lowerChecked compilation signatures expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalid invalidOperand missing definitions environment = .ok certified) :
    lower compilation signatures expression fuel source scope site assignment operator rhs outputType next reasonAt
      invalid invalidOperand missing = .ok certified.expression := by
  unfold lowerChecked at accepted
  obtain ⟨expression, generated, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; exact generated
  · cases accepted

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates
