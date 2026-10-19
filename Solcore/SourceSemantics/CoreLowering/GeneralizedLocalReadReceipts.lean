import Solcore.Frontend.SourceCoreLocalPolymorphism

/-! A successful generalized local read selects an exact cumulative instance
from the stored heterogeneous bundle. These receipts retain the compiler's
original and contextual nodes, native cell, and product projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

/-- Every field is an observation of the actual local-read compiler. The
complete substitution, rather than the candidate's result type, selects it. -/
structure Certificate (catalog : Catalog) (caller : Key) (active : Substitution)
    (source : TypedSource) (scope : Scope) (id : ExpressionId) (reason : Core.Word)
    (lowered : SourceCoreBasic.LoweredExpr) where
  sourceOwner : source.owner = caller.declaration
  readOwner : id.occurrence.owner = source.owner
  node : ExpressionNode
  nodeFound : source.lookupExpression? id = some node
  binder : Resolved.LocalId
  nodeForm : ∃ name, node.form = .reference name (.local binder)
  binderOwner : binder.owner = source.owner
  binding : Binding
  bindingFound : catalog.binding caller binder = .ok binding
  original : ExpressionNode
  originalFound : binding.source.lookupExpression? id = some original
  originalForm : ∃ name, original.form = .reference name (.local binder)
  rawType : active.apply original.rawType = node.rawType
  child : Substitution
  matched : SourceSpecialization.matchClosedSchemeInstance?
    (Scheme.apply active binding.binder.scheme) (active.apply original.rawType) = some child
  candidate : Instance
  instanceIndex : Nat
  selected : (binding.atContext active).zipIdx.filter (fun entry =>
    decide (entry.1.origin.substitution = child.compose active)) = [(candidate, instanceIndex)]
  resultType : node.type = candidate.origin.substitution.apply binding.binder.scheme.body
  index : Nat
  payloadType : Core.Ty
  slot : SourceCoreLocalCell.lookup? scope binder = some (index, payloadType)
  bundleType : binding.bundleType active = payloadType
  projection : Core.Expr
  projected : ProductBundle.project? ((binding.atContext active).map (·.type))
    instanceIndex (.var 0) = some projection
  emitted : lowered = ⟨candidate.type,
    SourceCoreLocalPolymorphism.read payloadType candidate.type (.var index) projection reason⟩

private theorem bind_ok {α β ε : Type} {computation : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem of_accepted {catalog : Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : lowerRead catalog caller active source scope id reason = .ok lowered) :
    Nonempty (Certificate catalog caller active source scope id reason lowered) := by
  unfold lowerRead at accepted
  dsimp only at accepted
  by_cases sourceOwner : source.owner = caller.declaration
  · rw [if_neg (not_not_intro sourceOwner)] at accepted
    try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
    by_cases readOwner : id.occurrence.owner = source.owner
    · rw [if_neg (not_not_intro readOwner)] at accepted
      try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
      cases nodeFound : source.lookupExpression? id with
      | none => simp [nodeFound, throw, throwThe, MonadExceptOf.throw] at accepted
      | some node =>
        simp only [nodeFound] at accepted
        cases nodeForm : node.form <;>
          try (solve | simp [nodeForm, throw, throwThe, MonadExceptOf.throw] at accepted)
        next name resolution =>
          cases resolution <;>
            try (solve | simp [nodeForm, throw, throwThe, MonadExceptOf.throw] at accepted)
          next binder =>
            simp only [nodeForm] at accepted
            by_cases binderOwner : binder.owner = source.owner
            · rw [if_neg (not_not_intro binderOwner)] at accepted
              try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
              obtain ⟨binding, bindingFound, accepted⟩ := bind_ok accepted
              try dsimp only at accepted
              cases originalFound : binding.source.lookupExpression? id with
              | none => simp [originalFound, throw, throwThe, MonadExceptOf.throw] at accepted
              | some original =>
                simp only [originalFound] at accepted
                cases originalForm : original.form <;>
                  try (solve | simp [originalForm, throw, throwThe, MonadExceptOf.throw] at accepted)
                next originalName resolution =>
                  cases resolution <;>
                    try (solve | simp [originalForm, throw, throwThe, MonadExceptOf.throw] at accepted)
                  next originalBinder =>
                    simp only [originalForm] at accepted
                    by_cases sameBinder : originalBinder = binder
                    · subst originalBinder
                      by_cases rawType : active.apply original.rawType = node.rawType
                      · have valid : (decide (binder ≠ binder) ||
                            decide (active.apply original.rawType ≠ node.rawType)) ≠ true := by
                          simp [rawType]
                        rw [if_neg valid] at accepted
                        try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
                        cases matched : SourceSpecialization.matchClosedSchemeInstance?
                            (Scheme.apply active binding.binder.scheme) (active.apply original.rawType) with
                        | none => simp [matched, throw, throwThe, MonadExceptOf.throw] at accepted
                        | some child =>
                          simp only [matched] at accepted
                          cases selected : (binding.atContext active).zipIdx.filter (fun entry =>
                              decide (entry.1.origin.substitution = child.compose active)) with
                          | nil => simp [selected, throw, throwThe, MonadExceptOf.throw] at accepted
                          | cons first rest =>
                            cases rest with
                            | cons next tail => simp [selected, throw, throwThe, MonadExceptOf.throw] at accepted
                            | nil =>
                              obtain ⟨candidate, instanceIndex⟩ := first
                              simp only [selected] at accepted
                              by_cases resultType : node.type =
                                  candidate.origin.substitution.apply binding.binder.scheme.body
                              · rw [if_neg (not_not_intro resultType)] at accepted
                                try dsimp only [bind, Except.bind, pure, Except.pure] at accepted
                                cases slot : SourceCoreLocalCell.lookup? scope binder with
                                | none => simp [slot, throw, throwThe, MonadExceptOf.throw] at accepted
                                | some slotValue =>
                                  obtain ⟨index, payloadType⟩ := slotValue
                                  simp only [slot] at accepted
                                  obtain ⟨_, checked, accepted⟩ := bind_ok accepted
                                  have bundleType : binding.bundleType active = payloadType := by
                                    by_cases same : binding.bundleType active = payloadType
                                    · exact same
                                    · simp [SourceCoreBasic.ensureType, same, Except.mapError] at checked
                                  cases projected : ProductBundle.project?
                                      ((binding.atContext active).map (·.type)) instanceIndex (.var 0) with
                                  | none => simp [projected, throw, throwThe, MonadExceptOf.throw] at accepted
                                  | some projection =>
                                    simp only [projected, Except.ok.injEq] at accepted
                                    exact ⟨{
                                      sourceOwner, readOwner, node, nodeFound, binder,
                                      nodeForm := ⟨name, nodeForm⟩, binderOwner,
                                      binding, bindingFound, original, originalFound,
                                      originalForm := ⟨originalName, originalForm⟩,
                                      rawType, child, matched, candidate, instanceIndex, selected,
                                      resultType, index, payloadType, slot, bundleType,
                                      projection, projected, emitted := accepted.symm
                                    }⟩
                              · simp [resultType, throw, throwThe, MonadExceptOf.throw] at accepted
                      · simp [rawType, throw, throwThe, MonadExceptOf.throw] at accepted
                    · simp [sameBinder, throw, throwThe, MonadExceptOf.throw] at accepted
            · simp [binderOwner, throw, throwThe, MonadExceptOf.throw] at accepted
    · simp [readOwner, throw, throwThe, MonadExceptOf.throw] at accepted
  · simp [sourceOwner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

variable {catalog : Catalog} {caller : Key} {active : Substitution}
  {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

theorem Certificate.candidate_at
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    (receipt.binding.atContext active)[receipt.instanceIndex]? = some receipt.candidate := by
  have member : (receipt.candidate, receipt.instanceIndex) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) := by
    rw [receipt.selected]
    exact List.mem_singleton_self _
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem Certificate.candidate_key
    (receipt : Certificate catalog caller active source scope id reason lowered) :
    receipt.candidate.origin.substitution = receipt.child.compose active := by
  have member : (receipt.candidate, receipt.instanceIndex) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) := by
    rw [receipt.selected]
    exact List.mem_singleton_self _
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The emitted position is unique even if different instances have equal
native function types. -/
theorem Certificate.unique_candidate
    (receipt : Certificate catalog caller active source scope id reason lowered)
    {candidate : Instance} {index : Nat}
    (stored : (receipt.binding.atContext active)[index]? = some candidate)
    (key : candidate.origin.substitution = receipt.child.compose active) :
    candidate = receipt.candidate ∧ index = receipt.instanceIndex := by
  have member : (candidate, index) ∈
      (receipt.binding.atContext active).zipIdx.filter (fun entry =>
        decide (entry.1.origin.substitution = receipt.child.compose active)) :=
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr stored, by simpa using key⟩
  rw [receipt.selected] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts
