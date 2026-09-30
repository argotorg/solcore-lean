import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates

/-! Static certificates for the executable basic statement lowerer.
The theorem consumes the actual successful compiler result, including all
metadata and scope checks. It assumes no source or Core execution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.BasicStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem bind_ok {α β : Type} {computation : Except SourceCoreBasic.Error α}
    {next : α → Except SourceCoreBasic.Error β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem projectType_types
    {site : SourceCoreElaboration.ErrorSite} {sourceType : Ty} {type : Core.Ty}
    (projected : SourceCoreBasic.projectType site sourceType = .ok type) :
    TypeRepresents sourceType type := by
  unfold SourceCoreBasic.projectType at projected
  cases result : SourceCoreElaboration.lowerType site sourceType with
  | error error => simp [result, Except.mapError] at projected
  | ok lowered =>
      simp only [result, Except.mapError, Except.ok.injEq] at projected
      subst lowered
      exact BasicExpressions.typeRepresents_of_lowerType result

structure Metadata (source : TypedSource) (id : StatementId)
    (node : StatementNode) (type : Core.Ty) : Prop where
  contains : ContainsStatement source id node
  owned : id.occurrence.owner = source.owner
  types : TypeRepresents node.type type

theorem readStatement_certificate
    {source : TypedSource} {id : StatementId} {node : StatementNode} {type : Core.Ty}
    (read : SourceCoreBasic.readStatement source id = .ok (node, type)) :
    source.lookupStatement? id = some node ∧ Metadata source id node type := by
  by_cases owned : id.occurrence.owner = source.owner
  · cases found : source.lookupStatement? id with
    | none => simp [SourceCoreBasic.readStatement, owned, found, bind, Except.bind] at read
    | some selected =>
        cases projected : SourceCoreBasic.projectType (.occurrence id.occurrence) selected.type with
        | error error =>
            simp [SourceCoreBasic.readStatement, owned, found, projected,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
        | ok projectedType =>
            simp [SourceCoreBasic.readStatement, owned, found, projected,
              bind, Except.bind, pure, Pure.pure, Except.pure] at read
            rcases read with ⟨rfl, rfl⟩
            exact ⟨rfl, lookupStatement?_sound found, owned, projectType_types projected⟩
  · simp [SourceCoreBasic.readStatement, owned, bind, Except.bind] at read

/-- These are executable binder restrictions, not the stronger declarative
`BinderExtends` judgment about the complete source static context. -/
structure BinderCertificate (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (binder : TypedBinder) (type : Core.Ty) : Prop where
  owned : binder.id.owner = source.owner
  monomorphic : binder.scheme.quantified = []
  requirements : binder.schemeRequirements = []
  runtime : binder.comptime = false
  fresh : scope.any (fun entry => decide (entry.1 = binder.id)) = false
  types : TypeRepresents binder.scheme.body type

theorem lowerBinder_certificate
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {type : Core.Ty}
    (accepted : SourceCoreBasic.lowerBinder source scope binder = .ok type) :
    BinderCertificate source scope binder type := by
  by_cases owned : binder.id.owner = source.owner
  · by_cases monomorphic : binder.scheme.quantified = []
    · by_cases requirements : binder.schemeRequirements = []
      · cases runtime : binder.comptime with
        | true =>
            simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
              runtime, bind, Except.bind] at accepted
        | false =>
            cases fresh : scope.any (fun entry => decide (entry.1 = binder.id)) with
            | true =>
                simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
                  runtime, fresh, bind, Except.bind] at accepted
            | false =>
                simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
                  runtime, fresh] at accepted
                exact ⟨owned, monomorphic, requirements, runtime, fresh, projectType_types accepted⟩
      · simp [SourceCoreBasic.lowerBinder, owned, monomorphic, requirements,
          bind, Except.bind] at accepted
    · simp [SourceCoreBasic.lowerBinder, owned, monomorphic,
        bind, Except.bind] at accepted
  · simp [SourceCoreBasic.lowerBinder, owned, bind, Except.bind] at accepted

structure AssignmentCertificate (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (index : Nat) (type : Core.Ty) : Prop where
  equal : operator = .equal
  owned : assignment.target.root.owner = source.owner
  requirements : assignment.requirements = []
  bare : assignment.target.projections = []
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, type)
  types : TypeRepresents assignment.target.type type

theorem lowerAssignment_certificate
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {index : Nat} {type : Core.Ty}
    (accepted : SourceCoreBasic.lowerAssignment source scope assignment operator = .ok (index, type)) :
    AssignmentCertificate source scope assignment operator index type := by
  by_cases equal : operator = .equal
  · by_cases owned : assignment.target.root.owner = source.owner
    · by_cases requirements : assignment.requirements = []
      · by_cases bare : assignment.target.projections = []
        · cases slot : SourceCoreLocalCell.lookup? scope assignment.target.root with
          | none =>
              simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare, slot,
                bind, Except.bind] at accepted
          | some found =>
              rcases found with ⟨foundIndex, foundType⟩
              simp only [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare, slot,
                ne_eq, not_true_eq_false, ↓reduceIte, List.isEmpty_nil,
                bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
              obtain ⟨projected, projection, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              cases accepted
              exact ⟨equal, owned, requirements, bare, slot, same ▸ projectType_types projection⟩
        · simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements, bare,
            bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      · simp [SourceCoreBasic.lowerAssignment, equal, owned, requirements,
          bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    · simp [SourceCoreBasic.lowerAssignment, equal, owned, bind, Except.bind] at accepted
  · simp [SourceCoreBasic.lowerAssignment, equal, bind, Except.bind] at accepted

private theorem expression_typing
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreBasic.lowerExpression fuel source scope id reason = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) ∧ Core.CellPayload lowered.type := by
  obtain ⟨_, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  exact ⟨tree.hasType, tree.cellPayload⟩

/-- All accepted basic statement lists have the declared Core result type.
Explicit returns intentionally need no certificate for their unreachable tail.
The scalar/product result invariant is extracted at the same time. -/
theorem lowerStatements_typing
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType resultType) ∧ Core.CellPayload resultType := by
  induction fuel generalizing scope statements expression with
  | zero =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
          · cases accepted
      | cons => cases accepted
  | succ fuel ih =>
      cases statements with
      | nil =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          split at accepted
          · rename_i unitResult
            subst resultType
            cases accepted
            exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
          · cases accepted
      | cons id rest =>
          simp only [SourceCoreBasic.lowerStatements] at accepted
          obtain ⟨⟨node, type⟩, read, accepted⟩ := bind_ok accepted
          cases form : node.form with
          | letDecl binder initializer =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
              have binderCertificate := lowerBinder_certificate binding
              cases initializer with
              | none =>
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  exact ⟨Core.LocalSequence.letUninitialized_hasType
                    (binderCertificate.types.wellFormed []) bodyTyped, resultPayload⟩
              | some initializer =>
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  have valueTyped := (expression_typing compiledValue).1
                  rw [← same] at valueTyped
                  exact ⟨Core.LocalSequence.letInitialized_hasType resultPayload.wellFormed
                    valueTyped bodyTyped, resultPayload⟩
          | assignValue assignment operator value =>
              simp only [form] at accepted
              obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
              cases checkedUnit
              obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
              obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
              cases checkedUnit
              have same := ensureType_ok checked
              obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
              have targetCertificate := lowerAssignment_certificate target
              have valueTyped := (expression_typing compiledValue).1
              rw [← same] at valueTyped
              exact ⟨Core.LocalSequence.assign_hasType resultPayload.wellFormed
                (.var (SourceCoreLocalCell.lookup?_context targetCertificate.slot))
                valueTyped bodyTyped, resultPayload⟩
          | returnStmt value =>
              cases value with
              | none =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, unitChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have resultSame := ensureType_ok resultChecked
                  have unitSame := ensureType_ok unitChecked
                  have resultUnit : resultType = .unit := resultSame.trans unitSame.symm
                  cases accepted
                  rw [resultUnit]
                  exact ⟨Core.LanguageResult.success_hasType .unit, .unit⟩
              | some value =>
                  simp only [form] at accepted
                  obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  have same := ensureType_ok checked
                  cases accepted
                  rw [same]
                  exact expression_typing compiledValue
          | expression value semicolon =>
              cases semicolon with
              | true =>
                  simp only [form, ↓reduceIte] at accepted
                  obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                  obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
                  cases accepted
                  obtain ⟨bodyTyped, resultPayload⟩ := ih compiledBody
                  exact ⟨Core.LocalSequence.discard_hasType resultPayload.wellFormed
                    (expression_typing compiledValue).1 bodyTyped, resultPayload⟩
              | false =>
                  simp only [form, Bool.false_eq_true, ↓reduceIte] at accepted
                  split at accepted
                  · obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
                    obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                    cases checkedUnit
                    have same := ensureType_ok checked
                    cases accepted
                    rw [same]
                    exact expression_typing compiledValue
                  · cases accepted
          | assignBitNot | ifThen | block | matchWith | forLoop | whileLoop | breakStmt | continueStmt =>
              simp [form] at accepted

theorem lowerStatements_hasType
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) expression
      (Core.LanguageResult.resultType resultType) :=
  (lowerStatements_typing accepted).1

theorem lowerStatements_infer
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {resultType : Core.Ty} {reason : Core.Word}
    {expression : Core.Expr}
    (accepted : SourceCoreBasic.lowerStatements fuel source scope statements resultType reason =
      .ok expression) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) expression =
      some (Core.LanguageResult.resultType resultType) :=
  Core.infer_complete (lowerStatements_hasType accepted)

end Solcore.SourceSemantics.CoreLowering.BasicStatements
