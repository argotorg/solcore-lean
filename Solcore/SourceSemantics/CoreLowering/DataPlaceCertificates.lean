import Solcore.SourceSemantics.CoreLowering.DataPlaceMembers

/-! Certificates extracted from accepted place compilation. They expose the
real generated helper, ordered index expressions and RHS, without assuming
any execution of those expressions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues

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

def KeyGenerated (expression : ExpressionLowerer) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word) (key : ExpressionId × Ty)
    (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  expression fuel source scope key.1 reasonAt = .ok lowered ∧ key.2 = lowered.type

theorem keys_generated {expression : ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {reasonAt : ExpressionId → Word} {keys : List (ExpressionId × Ty)}
    {lowered : List SourceCoreBasic.LoweredExpr}
    (accepted : keys.mapM (fun (id, expected) => do
      let key ← expression fuel source scope id reasonAt
      SourceCoreBasic.ensureType (.occurrence id.occurrence) expected key.type
      pure key) = .ok lowered) :
    ListRel (KeyGenerated expression fuel source scope reasonAt) keys lowered := by
  induction keys generalizing lowered with
  | nil => simp [List.mapM_nil, pure, Except.pure] at accepted; subst lowered; exact .nil
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, compiled, accepted⟩ := bind_ok accepted
    obtain ⟨rest, compiledRest, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst lowered
    obtain ⟨actual, generated, compiled⟩ := bind_ok compiled
    obtain ⟨checkedUnit, checked, compiled⟩ := bind_ok compiled
    cases checkedUnit
    simp only [pure, Except.pure, Except.ok.injEq] at compiled
    subst first
    exact .cons ⟨generated, ensureType_ok checked⟩ (ih compiledRest)

inductive RhsGenerated (expression : ExpressionLowerer) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word) (leafType : Ty) : Option ExpressionId → Expr → Prop where
  | absent : RhsGenerated expression fuel source scope reasonAt leafType none (LanguageResult.success .unit)
  | present {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      (generated : expression fuel source scope id reasonAt = .ok lowered)
      (type : leafType = lowered.type) :
      RhsGenerated expression fuel source scope reasonAt leafType (some id) lowered.expression

inductive Generated (checked : Checked) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Ty) (next : Expr) (reasonAt : ExpressionId → Word)
    (invalidProjection invalidOperand : Word) (missing : TypeSystem.Ty → Word) : Expr → Prop where
  | intro (route : Route) (prepared : Prepared) (index : Nat)
      (keys : List SourceCoreBasic.LoweredExpr) (value : Expr)
      (described : describe checked signatures source site assignment = .ok route)
      (lookup : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType))
      (preparedBy : prepare checked fuel route invalidProjection missing = .ok prepared)
      (keysGenerated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys keys)
      (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer)
      (rhsGenerated : RhsGenerated expression fuel source scope reasonAt route.leafType rhs value) :
      Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
        reasonAt invalidProjection invalidOperand missing
        (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value next outputType
          (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)

/-- The receipt follows actual successful compiler branches. It does not
replace or reinterpret the executable place compiler. -/
theorem generated_of_lower {checked : Checked} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word} {lowered : Expr}
    (accepted : lower checked signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
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
          Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
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

end Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
