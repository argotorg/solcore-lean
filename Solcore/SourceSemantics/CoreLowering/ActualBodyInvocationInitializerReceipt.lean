import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerBindingSelection
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt

/-! The actual initialized statement callback retains the same native binding
and ordered candidate receipts at either kind of body invocation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalInitializerCompilation (Receipt namedInputs)
open AcceptedContextualLambdaInitializerReceipt (contextualInputs)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- Literal inputs used by the named or contextual initializer callback. -/
def Index.initializerInputs (index : Index compiled bodyRelation) (fuel : Nat)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) : Inputs :=
  match index with
  | .named receipt _ => namedInputs receipt (fuel - 1) fuel index.compilation scope id reasonAt
  | .contextual material _ => contextualInputs material.inputs material.packet.original.emission.prepared
      material.packet.fuel (min fuel material.code.fuel) material.code.compilation scope id reasonAt

/-- These equalities come from the actual invocation receipts, including its
current owner and active substitution. -/
theorem Index.initializerInputs_fields (index : Index compiled bodyRelation) (fuel : Nat)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) :
    let inputs := index.initializerInputs fuel scope id reasonAt
    inputs.representation = (CallableIndexedNamedGeneration.representation compiled.indexed).atContext
      inputs.current.owner index.active ∧
    inputs.program = compiled.indexed.base.sourceProgram ∧
    inputs.locals = compiled.indexed.base.locals ∧
    inputs.native = compiled.indexed.base.callableContext ∧
    inputs.current.plan = compiled.indexed.base.plan ∧
    inputs.current.owner = index.owner ∧
    inputs.current.globals = compiled.indexed.base.globals ∧
    inputs.current.administrativePrefix = 1 ∧
    inputs.initializer = id ∧ inputs.scope = scope ∧ inputs.reasonAt = reasonAt := by
  cases index with
  | named receipt selected => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | contextual material view =>
    dsimp only [Index.initializerInputs, contextualInputs, Index.active, Index.owner]
    refine ⟨?_, material.indexed.program, material.indexed.locals, material.indexed.native, ?_, rfl, ?_, ?_, rfl, rfl, rfl⟩
    · unfold GeneralizedLocalLambdaCompilation.representation
      rw [material.indexed.represented, material.compilation, material.active]
      rfl
    · rw [material.compilation]; exact material.indexed.plan
    · rw [material.compilation]; exact material.indexed.globals
    · rw [material.compilation]; exact material.indexed.administrativePrefix

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem override_result {policy : SourceCoreFunctions.Policy}
    {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat} {current : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {special : SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
      TypedSource → SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
      Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr)}
    (hook : policy.lowerSpecial? = some special)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      current source scope id reasonAt = .ok lowered) :
    ∃ output, special current (FunctionCode.children policy body fuel current) (fuel + 1)
      source scope id reasonAt = .ok output ∧
      ∀ actual, output = some actual → lowered = actual := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    cases found : source.lookupExpression? id with
    | none => simp [found, bind, Except.bind] at accepted
    | some node =>
      simp only [found, bind, Except.bind, pure, Except.pure, hook] at accepted
      obtain ⟨output, selected, remaining⟩ := CompatibleEncoding.bind_ok accepted
      refine ⟨output, selected, ?_⟩
      intro actual same
      rw [same] at remaining
      exact (Except.ok.inj remaining).symm
  · simp [owner, bind, Except.bind] at accepted

private theorem named_special {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
    {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {initial : Binding} {output : Option SourceCoreBasic.LoweredExpr}
    (selected : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      current child budget source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      compiled.indexed.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compilation rootFuel budget current scope id reasonAt) binding [] lowered) := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  obtain ⟨viewed, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
  cases found : viewed.lookupExpression? id with
  | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | some node =>
    simp only [found, bind, Except.bind, pure, Except.pure, selected, Option.filter_some,
      ne_eq, reduceCtorEq, not_false_eq_true, decide_true, ↓reduceIte] at accepted
    obtain ⟨binding, located, accepted⟩ := CompatibleEncoding.bind_ok accepted
    obtain ⟨lowered, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
    exact ⟨binding, lowered, (Except.ok.inj accepted).symm, mapError_ok located,
      GeneralizedLocalInitializerCompilation.of_accepted (mapError_ok generated)⟩

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
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

/-- The generalized branch of the actual statement binder policy. -/
theorem Index.generalized_binder (index : Index compiled bodyRelation)
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (generalized : binder.scheme.quantified ≠ [])
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload) :
    lowerBinder compiled.indexed.base.locals index.owner index.active
      index.compilerSource scope binder = .ok payload := by
  have nonempty : binder.scheme.quantified.isEmpty = false := by cases q : binder.scheme.quantified <;> simp_all
  cases index with
  | named receipt selected =>
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _ at projected
    unfold SourceCoreGeneralFunctions.contextualBinder at projected
    rw [nonempty] at projected
    exact mapError_ok projected
  | contextual material view =>
    change SourceCoreGeneralFunctions.contextualBinder _ material.inputs.locals material.inputs.current.owner
      material.packet.original.emission.prepared.substitution material.code.view scope binder = _ at projected
    unfold SourceCoreGeneralFunctions.contextualBinder at projected
    rw [nonempty] at projected
    have accepted := mapError_ok projected
    change lowerBinder _ material.code.compilation.owner material.code.active _ _ _ = _
    rw [material.compilation, material.active, ← material.indexed.locals]
    exact accepted

/-- The actual `Tree.initialized` data identifies the complete native binding
and its exact initializer compilation receipt. Ordinary binders take their own
compiler branch and are not inputs to this endpoint. -/
theorem Index.initialized_compilation_receipt (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {stored : Ty}
    (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : node.form = .letDecl binder (some initializer))
    (generalized : binder.scheme.quantified ≠ [])
    {scope : SourceCoreLocalCell.Scope} {payload : Ty}
    (projected : index.policy.lowerBinder index.compilerSource scope binder = .ok payload)
    {fuel : Nat} {reasonAt : ExpressionId → Word} {child : SourceCoreBasic.LoweredExpr}
    (generated : index.policy.lowerExpression fuel index.compilerSource scope initializer reasonAt = .ok child) :
    ∃ binding, compiled.indexed.base.locals.binding index.owner binder.id = .ok binding ∧
      binding.binder.applySubstitution index.active = binder ∧
      binding.initializer = initializer ∧ binding.source = index.originalSource ∧
      payload = binding.bundleType index.active ∧
      Nonempty (Receipt (index.initializerInputs fuel scope initializer reasonAt) binding index.active child) := by
  have found := read
  rw [index.statement_reader] at found
  have found := read_found found
  obtain ⟨binding, located, selected, metadata, initEq, source, payloadEq⟩ :=
    index.initialized_binding_selected artifact checked found form (index.generalized_binder generalized projected)
  refine ⟨binding, located, metadata, initEq, source, payloadEq, ?_⟩
  cases index with
  | named receipt record =>
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ predecessor =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt record] at generated
      obtain ⟨output, accepted, result⟩ := override_result rfl generated
      obtain ⟨actual, lowered, sameOutput, actualLocated, compiledReceipt⟩ := named_special receipt selected accepted
      have sameLowered := result lowered sameOutput
      subst lowered
      have bindingId : binding.binder.id = binder.id := by
        simpa only [TypedBinder.applySubstitution] using congrArg TypedBinder.id metadata
      rw [bindingId] at actualLocated
      have same : actual = binding := Except.ok.inj (actualLocated.symm.trans located)
      subst actual
      exact compiledReceipt
  | contextual material view =>
    have different := (Index.contextual material view).initializer_ne_body_lambda artifact checked
      material.code.found (material.code.form.trans material.code.sourceForm) reached found form
    rw [material.codeId] at different
    change (GeneralizedLocalAcceptedBodyCompiler.policy material).lowerExpression _ _ _ _ _ = _ at generated
    rw [GeneralizedLocalAcceptedBodyCompiler.expression_reader] at generated
    unfold FunctionCode.children at generated
    rw [material.policy] at generated
    cases budgetEq : min fuel material.code.fuel with
    | zero => simp [budgetEq, SourceCoreFunctions.lowerExpressionWithPolicy] at generated
    | succ predecessor =>
      rw [budgetEq] at generated
      obtain ⟨output, actual, result⟩ := override_result rfl generated
      change GeneralizedLocalLambdaCompilation.special material.inputs material.packet.original.emission.prepared
        material.packet.fuel material.code.compilation _ (predecessor + 1) _ _ _ _ = _ at actual
      have chosen : material.inputs.locals.bindings.find? (fun entry =>
          decide (entry.caller = material.code.compilation.owner ∧ entry.initializer = initializer)) = some binding := by
        rw [material.indexed.locals]
        exact selected
      obtain ⟨actualBinding, lowered, sameOutput, actualLocated, sameBinding, _, compiledReceipt⟩ :=
        AcceptedContextualLambdaInitializerReceipt.of_special_output chosen different actual
      subst actualBinding
      have sameChild := result lowered sameOutput
      subst lowered
      change Nonempty (Receipt (contextualInputs material.inputs material.packet.original.emission.prepared
        material.packet.fuel (min fuel material.code.fuel) material.code.compilation scope initializer reasonAt)
        binding material.code.active child)
      rw [budgetEq, material.active]
      exact compiledReceipt

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
