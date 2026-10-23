import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates

/-! A successful native generalized initializer cannot retain evidence on its
lambda header. The actual coercion spine and the compiler's decreasing fuel
supply this fact before the existing lambda packet is constructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs Receipt)
open GeneralizedLocalLambdaCompilation

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem emit_inRight {reason : Word} {input raw : Expr}
    {calls : List CallableCoercionSpine.Call}
    (shape : CallableCoercionSpine.emit reason input calls = .inRight .word raw) :
    calls = [] := by
  induction calls generalizing input with
  | nil => rfl
  | cons head tail ih =>
    have empty := ih shape
    subst empty
    simp [CallableCoercionSpine.emit, SourceCoreCalls.call, LanguageResult.bind] at shape

/-- Actual successful output coercions cannot produce an unwrapped successful
closure expression unless the original ordered coercion list is empty. -/
theorem coercions_empty {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {context : SourceCoreFunctions.Context} {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : SourceCoreBasic.LoweredExpr} {steps : List CoercionStep} {raw : Expr}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy
      input steps = .ok output)
    (shape : output.expression = .inRight .word raw) : steps = [] := by
  obtain ⟨calls, spine⟩ := CallableCoercionSpine.of_accepted accepted
  have empty := emit_inRight (spine.code.symm.trans shape)
  have length := spine.length
  rw [empty] at length
  cases steps <;> simp_all

/-- Replacing the expression found by the actual first-match lookup preserves
that lookup. Occurrence uniqueness is not needed for this local operation. -/
theorem replaced_lookup {source : TypedSource} {id : ExpressionId} {node replacement : ExpressionNode}
    (found : source.lookupExpression? id = some node) (same : replacement.id = node.id) :
    (SourceCoreEvidence.withNode source replacement).lookupExpression? id = some replacement := by
  have nodeId : node.id = id := (lookupExpression?_sound found).2
  have replacementId : replacement.id = id := same.trans nodeId
  rcases source with ⟨owner, inputs, roots, nodes⟩
  unfold SourceCoreEvidence.withNode TypedSource.lookupExpression? TypedSource.lookupNode? at *
  dsimp only at *
  induction nodes with
  | nil => cases found
  | cons current rest ih =>
    cases current with
    | statement statement =>
      cases hit : decide ((Node.statement statement).occurrenceId = id.occurrence)
      · simp only [List.find?_cons, hit] at found
        simpa only [List.map_cons, List.find?_cons, hit] using ih found
      · simp only [List.find?_cons, hit] at found
        cases found
    | expression expression =>
      by_cases hit : expression.id = id
      · subst hit
        simp [List.map_cons, replacementId, Node.occurrenceId, Node.id,
          NodeId.occurrenceId]
      · have occurrence : expression.id.occurrence ≠ id.occurrence := by
          intro equal
          exact hit (congrArg ExpressionId.mk equal)
        have different : expression.id ≠ replacement.id := by simpa only [replacementId] using hit
        simp only [List.find?_cons, Node.occurrenceId, Node.id, NodeId.occurrenceId,
          occurrence, decide_false] at found
        simpa only [List.map_cons, different, ↓reduceIte, List.find?_cons, Node.occurrenceId,
          Node.id, NodeId.occurrenceId, occurrence, decide_false] using ih found

private theorem special_lambda (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (policyFuel budget : Nat) (child : SourceCoreFunctions.ExpressionLowerer)
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {reasonAt : ExpressionId → Word}
    (found : source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    special inputs prepared policyFuel (context inputs prepared) child budget source scope
      inputs.initializer reasonAt =
    SourceCoreEvidence.lowerWithProjector inputs.program
      (representation inputs prepared).expressions.projectType prepared.caller (context inputs prepared)
      child budget source scope inputs.initializer reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) := by
  have skipped : (inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context inputs prepared).owner ∧ binding.initializer = inputs.initializer))).filter
      (fun _ => decide (some inputs.initializer ≠ some inputs.initializer)) = none := by simp
  simp only [special, SourceCoreGeneralFunctions.contextualSource, found, form,
    bind, Except.bind, pure, Except.pure, skipped]
  cases SourceCoreEvidence.lowerWithProjector inputs.program
    (representation inputs prepared).expressions.projectType prepared.caller (context inputs prepared)
    child budget source scope inputs.initializer reasonAt
    (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) with
  | error error => rfl
  | ok value => cases value <;> rfl

private theorem evidence_none {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {context : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (accepted : SourceCoreEvidence.lowerWithProjector program project caller context child fuel source scope
      id reasonAt policy = .ok none) : node.requirements = [] ∧ node.coercions = [] := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure] at accepted
  cases ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp [ordinary] at accepted
  | some requirements =>
    simp only [ordinary, Bool.not_false,
      Bool.and_true, Bool.or_false] at accepted
    split at accepted
    · rename_i empty
      have e : node.coercions = [] ∧ node.requirements = [] := by simpa using empty
      exact e.symm
    · by_cases valid : node.hasValidCoercionPath = true
      · by_cases owner : caller.key = context.owner
        · simp only [valid, owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
          split at accepted
          · cases accepted
          · split at accepted
            · cases accepted
            · split at accepted
              · cases accepted
              · split at accepted
                · cases accepted
                · split at accepted
                  · cases accepted
                  · split at accepted
                    · cases accepted
                    · split at accepted <;> cases accepted

        · simp [valid, owner] at accepted
      · simp [valid] at accepted


/-- The same actual contextual policy is fixed while its remaining expression
fuel decreases. Only the lambda currently being emitted is examined. -/
theorem lowered_metadata (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (policyFuel fuel : Nat) {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr} {raw : Expr}
    (found : source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy
      (policy inputs prepared policyFuel) (lowerBody inputs prepared) fuel (context inputs prepared)
      source scope inputs.initializer reasonAt = .ok lowered)
    (shape : lowered.expression = .inRight .word raw) :
    node.requirements = [] ∧ node.coercions = [] := by
  induction fuel generalizing source node lowered with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
  | succ fuel ih =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
    dsimp only at accepted
    by_cases owner : inputs.initializer.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      change (do
        let special ← special inputs prepared policyFuel (context inputs prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs prepared policyFuel)
              (lowerBody inputs prepared) (min budget fuel) (context inputs prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) source scope inputs.initializer reasonAt
        if let some result := special then pure result else _) = .ok lowered at accepted
      rw [special_lambda inputs prepared policyFuel (fuel + 1) _ found form] at accepted
      obtain ⟨evidence, evidenceAccepted, accepted⟩ := bind_ok accepted
      cases evidence with
      | none => exact evidence_none found form evidenceAccepted
      | some value =>
        have same : value = lowered := Except.ok.inj accepted
        subst value
        cases ordinaryEq : SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | none =>
          simp only [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryEq,
            bind, Except.bind, pure, Except.pure] at evidenceAccepted
          cases evidenceAccepted
        | some ordinary =>
          obtain ⟨delegated⟩ := CallableCoercionExpressionCertificates.delegated_of_accepted found
            ordinaryEq (by simp [CallableCoercionExpressionCertificates.Delegates, form]) evidenceAccepted
          have empty := coercions_empty delegated.suffix.accepted shape
          have normal : SourceCompilationPlan.ordinaryOwnedRequirements? node = some node.requirements := by
            unfold SourceCompilationPlan.ordinaryOwnedRequirements?
            rw [empty]
            change (if node.requirements.length < 0 then none else
              let owned := node.requirements.take (node.requirements.length - 0)
              if node.requirements = owned ++ [] then some owned else none) = some node.requirements
            simp
          have ordinarySame : delegated.ordinary = node.requirements :=
            Option.some.inj (delegated.ordinaryAccepted.symm.trans normal)
          have childFound := replaced_lookup (replacement := CallableCoercionExpressionCertificates.rawNode node delegated.ordinary)
            found rfl
          have childShape : delegated.operand.expression = .inRight .word raw := by
            have sameOutput := delegated.suffix.accepted
            simp only [empty, SourceCoreEvidence.applyCoercions, pure, Except.pure, Except.ok.injEq] at sameOutput
            exact congrArg SourceCoreBasic.LoweredExpr.expression sameOutput |>.trans shape
          have childAccepted := delegated.childAccepted
          simp only [Nat.min_eq_right (Nat.le_succ fuel)] at childAccepted
          have metadata := ih childFound (by simpa [CallableCoercionExpressionCertificates.rawNode] using form)
            childAccepted childShape
          exact ⟨by simpa only [CallableCoercionExpressionCertificates.rawNode, ordinarySame] using metadata.1, empty⟩
    · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Metadata emptiness follows from the compiler result retained by the actual
instance receipt, independently of the source closure's runtime metadata. -/
theorem receipt_metadata {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    node.requirements = [] ∧ node.coercions = [] := by
  have accepted := receipt.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs receipt.emission.prepared budget] at accepted
    exact lowered_metadata inputs receipt.emission.prepared fuel (fuel + 1) found form accepted receipt.extracted

/-- Once the actual special callback is excluded, the compiler's ordinary
lambda branch contains this representation read, with the same source and ID. -/
theorem receipt_read {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) :
    inputs.initializer.occurrence.owner = receipt.emission.prepared.source.owner ∧
    ∃ actual reported, inputs.representation.expressions.readExpression receipt.emission.prepared.source
      inputs.initializer = .ok (actual, reported) := by
  obtain ⟨requirements, coercions⟩ := receipt_metadata receipt found form
  have accepted := receipt.compiled
  cases budget : min inputs.budget inputs.fuel with
  | zero => simp [Inputs.child, budget, SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [child_at_succ inputs receipt.emission.prepared budget,
      SourceCoreFunctions.lowerExpressionWithPolicy.eq_def] at accepted
    dsimp only at accepted
    by_cases owner : inputs.initializer.occurrence.owner = receipt.emission.prepared.source.owner
    · refine ⟨owner, ?_⟩
      simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
        bind, Except.bind, pure, Except.pure] at accepted
      change (do
        let special ← special inputs receipt.emission.prepared fuel (context inputs receipt.emission.prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs receipt.emission.prepared fuel)
              (lowerBody inputs receipt.emission.prepared) (min budget fuel) (context inputs receipt.emission.prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) receipt.emission.prepared.source inputs.scope inputs.initializer inputs.reasonAt
        if let some result := special then pure result else _) = .ok receipt.lowered at accepted
      rw [special_lambda inputs receipt.emission.prepared fuel (fuel + 1) _ found form] at accepted
      have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
        unfold SourceCompilationPlan.ordinaryOwnedRequirements?
        rw [requirements, coercions]
        rfl
      have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
          (representation inputs receipt.emission.prepared).expressions.projectType receipt.emission.prepared.caller
          (context inputs receipt.emission.prepared)
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy (policy inputs receipt.emission.prepared fuel)
              (lowerBody inputs receipt.emission.prepared) (min budget fuel) (context inputs receipt.emission.prepared)
              childSource childScope childId childReasonAt)
          (fuel + 1) receipt.emission.prepared.source inputs.scope inputs.initializer inputs.reasonAt
          (SourceCoreGeneralFunctions.callablePolicy inputs.native receipt.emission.prepared.substitution) = .ok none := by
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          bind, Except.bind, pure, Except.pure]
      rw [evidence] at accepted
      simp only [bind, Except.bind, form] at accepted
      change (do
        let read ← (policy inputs receipt.emission.prepared fuel).readExpression
          receipt.emission.prepared.source inputs.initializer
        _) = .ok receipt.lowered at accepted
      obtain ⟨pair, read, _⟩ := bind_ok accepted
      rcases pair with ⟨actual, reported⟩
      refine ⟨actual, reported, ?_⟩
      simpa [policy, SourceCoreGeneralFunctions.contextualSource, found, form,
        representation, SourceCoreGeneralFunctions.Representation.atContext] using read
    · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- For the actual compatible reader, its retained lookup identifies the same
lambda node. The original packet constructor then needs no assumed metadata. -/
theorem packet_of_compatible {inputs : Inputs} {candidate : Instance} {raw : Expr}
    (receipt : Receipt inputs candidate raw)
    {checked : SourceCoreCompatibleCatalog.Checked}
    (reader : inputs.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression checked)
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId}
    (found : receipt.emission.prepared.source.lookupExpression? inputs.initializer = some node)
    (form : node.form = .lambda parameters result body) : Nonempty (Packet inputs candidate raw) := by
  obtain ⟨owner, actual, reported, read⟩ := receipt_read receipt found form
  have metadata := CompatibleExpressionReads.metadata_of_read (reader ▸ read)
  have same : actual = node := Option.some.inj (metadata.found.symm.trans found)
  subst actual
  exact of_receipt receipt found form owner metadata.requirements metadata.coercions read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
