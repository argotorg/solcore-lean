import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyReads
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles

/-!
# Body invocations: initializers and allocation

Initializer receipts of a body invocation, captured allocation and its attachment, and header binders.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompilerProgramAdmission
/-! Whole-program clients reuse the selected compilation producer. Their
existing validity receipt supplies the selected body facts internally. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompilerProgramAdmission
open Core Frontend SourceInference
open CompilerProgramStaticProfile
open SelectedCompilationPreparedProgramCertificates (Certificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Actual indices retain the complete original named carrier. -/
theorem profile_at {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (profile : StaticProfile compiled) (selected : compiled.indexed.base.functions[index]? = some named) :
    Nonempty (Row compiled named profile.table.rows) :=
  SelectedCompilationProgramAdmission.profile_at profile selected

/-- The existing full-program interface uses the same compiler certificate
producer, including its original dictionary and closed coercion alternatives. -/
theorem of_profile (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : StaticProfile compiled) : Nonempty (Certificate compiled) :=
  SelectedCompilationProgramAdmission.of_profile checked
    (SelectedCompilationBodyTyping.Bodies.of_program wellFormed) profile

end Solcore.SourceSemantics.CoreLowering.AcceptedCompilerProgramAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInitializerReceipt
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAcceptedInitializer
/-! The actual reached initialized statement supplies the existing accepted
bundle receipt, including empty bundles and contextual invocations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference SourceCoreLocalPolymorphism

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

theorem Index.initialized_accepted_receipt (index : Index compiled bodyRelation)
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
      Nonempty (GeneralizedLocalAcceptedInitializer.Receipt compiled.indexed
        (index.initializerInputs fuel scope initializer reasonAt) binding index.active child) := by
  obtain ⟨binding, located, metadata, initial, source, payloadEq, original⟩ :=
    index.initialized_compilation_receipt artifact checked reached read form generalized projected generated
  obtain ⟨original⟩ := original
  obtain ⟨represented, program, locals, native, plan, owner, globals, administrative,
      initializerEq, _scope, _reason⟩ :=
    index.initializerInputs_fields fuel scope initializer reasonAt
  refine ⟨binding, located, metadata, initial, source, payloadEq, ?_⟩
  exact SelectedCompilationInitializerRows.of_receipt compiled
    (owner.symm ▸ located) (initializerEq.trans initial.symm) represented
    program locals native plan globals administrative original

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationCapturedAllocation
/-! A successful binder compiler checks the actual binder metadata. Together
with the accepted candidate, this attaches captured scope to the same stored
Snapshot at an initialized statement or loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalAcceptedInstances (Snapshot)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : BodyRelation} {index : Index compiled bodyRelation}

theorem Index.ResidualEntry.capture_binding_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (form : statement.form = .letDecl binder (some binding.initializer))
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (member : candidate ∈ binding.atContext index.active) :
    CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified index.active.domain := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have source := index.binding_original indexed ownLocated member owner
  have captured := entry.capture_statement site found form
  rw [SourceCoreLocalPolymorphism.lowerBinder_quantified lowered located] at captured
  simpa only [source] using captured

theorem Index.ResidualEntry.capture_binding_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (present : .letDecl binder (some binding.initializer) ∈ initializers ++ post)
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (member : candidate ∈ binding.atContext index.active) :
    CapturedResidualScope binding.source binding.initializer
      binding.binder.scheme.quantified index.active.domain := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have source := index.binding_original indexed ownLocated member owner
  have captured := entry.capture_header site found form present
  rw [SourceCoreLocalPolymorphism.lowerBinder_quantified lowered located] at captured
  simpa only [source] using captured

theorem Index.ResidualEntry.retain_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (form : statement.form = .letDecl binder (some binding.initializer))
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (member : candidate ∈ binding.atContext index.active)
    (snapshot : Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalReachedAllocation.Attachment function binding index.active) candidate native) :
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate native := by
  apply GeneralizedLocalCapturedScopes.retain_scope snapshot
  cases snapshot with
  | retained packet indexed acceptedBody sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact entry.capture_binding_statement site found form lowered located indexed member

theorem Index.ResidualEntry.retain_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binding : SourceCoreLocalPolymorphism.Binding} {binder : TypedBinder}
    (present : .letDecl binder (some binding.initializer) ∈ initializers ++ post)
    {scope : SourceCoreLocalCell.Scope} {type : Core.Ty}
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope binder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {location : Core.Location}
    {candidate : SourceCoreLocalPolymorphism.Instance} {native : Core.Value}
    (member : candidate ∈ binding.atContext index.active)
    (snapshot : Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalReachedAllocation.Attachment function binding index.active) candidate native) :
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate native := by
  apply GeneralizedLocalCapturedScopes.retain_scope snapshot
  cases snapshot with
  | retained packet indexed acceptedBody sameLexical owner initializer candidateSource candidateBinder
      attached origin frame declarations ownership issuer reference typed runtimeTyped =>
    exact entry.capture_binding_header site found form present lowered located indexed member

/-! The actual native frame creation consumes the scope above, retaining the
same evaluation and strengthening only the stored proof component. -/
theorem Index.ResidualEntry.form_statement_at_actual_frame
    (index : Index compiled ReachedView) (entry : index.ResidualEntry)
    {statementId : StatementId} (site : index.Site (.statement statementId))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? statementId = some statement)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    {allocatedBinder : TypedBinder} {type : Core.Ty}
    (form : statement.form = .letDecl allocatedBinder (some binding.initializer))
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource inputs.scope allocatedBinder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner allocatedBinder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) := by
  obtain ⟨currentOwner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [currentOwner, binderId] using located
  obtain ⟨evaluation, snapshot⟩ := GeneralizedLocalReachedAllocation.formation_at_actual_frame index
    indexed ownLocated member sameLexical owner currentOwner initializer sameSource captures unique
    reached origin captured declarations ownership issuer typed stored reference read
  exact ⟨evaluation, entry.retain_statement site found form lowered located member snapshot⟩

theorem Index.ResidualEntry.form_header_at_actual_frame
    (index : Index compiled ReachedView) (entry : index.ResidualEntry)
    {statementId : StatementId} (site : index.Site (.statement statementId))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? statementId = some statement)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    {actual : Core.Environment}
    {allocatedBinder : TypedBinder} {type : Core.Ty}
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    (present : .letDecl allocatedBinder (some binding.initializer) ∈ initializers ++ post)
    (lowered : SourceCoreLocalPolymorphism.lowerBinder compiled.indexed.base.locals
      index.owner index.active index.compilerSource inputs.scope allocatedBinder = .ok type)
    (located : compiled.indexed.base.locals.binding index.owner allocatedBinder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (sameLexical : indexed.lexical = index.active)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer))
    (origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding index.active location
      (GeneralizedLocalCapturedScopes.Attachment function binding index.active) candidate
      (GeneralizedLocalInstanceValues.value indexed captured.embedding origin.native actual) := by
  obtain ⟨currentOwner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have ownLocated : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [currentOwner, binderId] using located
  obtain ⟨evaluation, snapshot⟩ := GeneralizedLocalReachedAllocation.formation_at_actual_frame index
    indexed ownLocated member sameLexical owner currentOwner initializer sameSource captures unique
    reached origin captured declarations ownership issuer typed stored reference read
  exact ⟨evaluation, entry.retain_header site found form present lowered located member snapshot⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationAttachment
/-! The actual reached capture supplies its stored attachment even when its
native bundle has no candidate rows. The original binding source is supplied
by the real initialized statement compiler. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem
open CallableBodyMetadataViews CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {index : Index compiled ReachedView}

private theorem capture_roots {function : Dynamic.GeneralizedClosure}
    {roots : List NodeId}
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : Reaches function.source roots (.expression function.initializer)) :
    ∀ id ∈ lambdaRoots function.initializer function.body, Reaches function.source roots id := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  intro id member
  rcases List.mem_cons.mp member with same | inBody
  · exact same ▸ reached
  · apply Reaches.expression reached found
    simpa only [form, ExpressionForm.references] using inBody

/-- This attachment uses the actual invocation and full native binding
origin. It does not require any candidate to exist in the bundle. -/
theorem Index.allocation_attachment (index : Index compiled ReachedView)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    (source : binding.source = index.originalSource)
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer)) :
    GeneralizedLocalReachedAllocation.Attachment function binding index.active := by
  have view : BodyView function.source index.compilerSource (index.statements.map NodeId.statement) := by
    rw [sameSource]
    exact index.reached_view
  have actualReached : Reaches function.source (index.statements.map NodeId.statement)
      (.expression function.initializer) := view.symm.reaches reached
  refine ⟨GeneralizedLocalPreparedClosure.invocation_closed index, ?_⟩
  rw [source, ← index.compiler_original]
  exact view.restrict (capture_roots captures unique actualReached)

/-- A real statement site adds its lexical residual scope to the same
attachment, ready for storage and later contextual reads. -/
theorem Index.ResidualEntry.statement_attachment (entry : index.ResidualEntry)
    {id : StatementId} (site : index.Site (.statement id))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {binding : SourceCoreLocalPolymorphism.Binding}
    (form : statement.form = .letDecl binder (some binding.initializer))
    (source : binding.source = index.originalSource)
    (metadata : binding.binder.applySubstitution index.active = binder)
    {function : Dynamic.GeneralizedClosure}
    (sameSource : function.source = index.source)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (reached : index.Reached (.expression function.initializer)) :
    GeneralizedLocalCapturedScopes.Attachment function binding index.active := by
  refine ⟨index.allocation_attachment source sameSource captures unique reached, ?_⟩
  have captured := entry.capture_statement site found form
  have quantified : binding.binder.scheme.quantified = binder.scheme.quantified := by
    simpa only [TypedBinder.applySubstitution, Scheme.apply] using
      congrArg (fun actual : TypedBinder => actual.scheme.quantified) metadata
  simpa only [source, quantified] using captured

/-- A captured descriptor keeps this invocation's actual frame and its
reached lexical attachment. The native binding can have an empty bundle. -/
theorem Index.ResidualEntry.descriptor_at_statement (entry : index.ResidualEntry)
    (frame : Frame index)
    {id : StatementId} (site : index.Site (.statement id))
    {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer))
    {binding : SourceCoreLocalPolymorphism.Binding}
    (located : compiled.indexed.base.locals.binding index.owner binder.id = .ok binding)
    (metadata : binding.binder.applySubstitution index.active = binder)
    (initial : binding.initializer = initializer)
    (source : binding.source = index.originalSource)
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context index.source environment
      binder initializer function)
    (unique : NodeOccurrencesUnique index.source) :
    ∃ origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active,
      origin.native = frame.native ∧ origin.ghost = frame.ghost ∧ origin.metadata = frame.metadata ∧
      GeneralizedLocalCapturedScopes.Attachment function binding index.active ∧
      Nonempty (GeneralizedLocalLocatedRows.Attachment
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed GeneralizedLocalCapturedScopes.Attachment)
        function binding index.active) := by
  obtain ⟨owner, binderId⟩ := SourceCoreLocalPolymorphism.Catalog.binding_identity located
  have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding := by
    simpa only [owner, binderId] using located
  have selfCapture : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
      function.captured function.binder function.initializer function := by
    simpa only [captures.definitionContext_eq, captures.source_eq, captures.captured_eq,
      captures.binder_eq, captures.initializer_eq] using captures
  have reached : index.Reached (.expression function.initializer) := by
    rw [captures.initializer_eq]
    exact .statement site.reached found (by simp [form, StatementForm.references])
  let origin : GeneralizedLocalDescriptorOrigin.Origin compiled.indexed function binding index.active := {
    native := frame.native
    ghost := frame.ghost
    metadata := frame.metadata
    carried := frame.carried
    paired := captures.source_eq.symm ▸ frame.paired
    owner := frame.owner.trans owner.symm
    active := frame.active }
  have attached := entry.statement_attachment site found (initial.symm ▸ form)
    source metadata captures.source_eq selfCapture (captures.source_eq.symm ▸ unique) reached
  exact ⟨origin, rfl, rfl, rfl, attached,
    ⟨⟨registered, selfCapture, ⟨origin⟩,
      (congrArg TypedBinder.id captures.binder_eq).trans binderId.symm,
      captures.initializer_eq.trans initial.symm⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationHeaderBinders
/-! The actual native catalog is built from statement declarations. A header
binder accepted by the same policy is therefore monomorphic: source ownership
prevents a header and a catalog statement from defining the same local ID. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference SourceCoreLocalPolymorphism

private theorem same_node_of_defined {nodes : List Node}
    (unique : (nodes.flatMap Node.definedLocalIds).Nodup)
    {left right : Node} (lm : left ∈ nodes) (rm : right ∈ nodes)
    {id : Resolved.LocalId} (ld : id ∈ left.definedLocalIds) (rd : id ∈ right.definedLocalIds) :
    left = right := by
  induction nodes with
  | nil => cases lm
  | cons head rest ih =>
    obtain ⟨_, tailUnique, disjoint⟩ := List.nodup_append.mp unique
    rcases List.mem_cons.mp lm with leftHead | leftTail
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact leftHead.trans rightHead.symm
      · exact False.elim (disjoint id (leftHead ▸ ld) id
          (List.mem_flatMap.mpr ⟨right, rightTail, rd⟩) rfl)
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact False.elim (disjoint id (rightHead ▸ rd) id
          (List.mem_flatMap.mpr ⟨left, leftTail, ld⟩) rfl)
      · exact ih tailUnique leftTail rightTail


private theorem binding_member {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} (located : catalog.binding caller binder = .ok binding) :
    binding ∈ catalog.bindings := by
  unfold Catalog.binding at located
  split at located
  · cases located
  · next actual only =>
    cases located
    have member : binding ∈ [binding] := List.mem_singleton_self _
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases located

/-- The concrete accepted header policy cannot select a generalized native
statement binding at a distinct source definition. No header restriction is
assumed: the result follows from that policy's success and checked ownership. -/
theorem Index.header_binder_monomorphic
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {fuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace fuel = .ok sourceCompiled.program)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initial condition post body)
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (present : ForItemForm.letDecl binder initializer ∈ initial ++ post)
    {scope : Scope} {type : Ty}
    (accepted : index.policy.lowerBinder index.compilerSource scope binder = .ok type) :
    binder.scheme.quantified = [] := by
  by_cases generalized : binder.scheme.quantified = []
  · exact generalized
  exfalso
  obtain ⟨binding, located, _metadata, _type⟩ := lowerBinder_success (index.generalized_binder generalized accepted)
  obtain ⟨origin, owner, sameId⟩ := SelectedCompilationBindingOrigins.at_binding compiled located
  have sameSource := index.native_binding_source (binding_member located) owner
  obtain ⟨recorded, recordedMember, recordedForm⟩ := origin.statement
  rw [sameSource] at recordedMember
  have ownership : LocalIdentityOwnership index.compilerSource := by
    rw [index.compiler_original]
    exact FlexibleSubstitution.LocalIdentityOwnership.applySubstitution index.active
      (index.original_source_resources artifact checked).2
  have unique : (index.compilerSource.nodes.flatMap Node.definedLocalIds).Nodup :=
    (List.nodup_append.mp (show (index.compilerSource.inputs.map (·.id) ++
        index.compilerSource.nodes.flatMap Node.definedLocalIds).Nodup from by
      simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.1
  have recordedApplied : Node.statement (recorded.applySubstitution index.active) ∈ index.compilerSource.nodes := by
    rw [index.compiler_original]
    exact List.mem_map.mpr ⟨.statement recorded, recordedMember, rfl⟩
  have recordedId : binder.id ∈ (Node.statement (recorded.applySubstitution index.active)).definedLocalIds := by
    simp only [Node.definedLocalIds, StatementForm.definedLocalIds,
      StatementNode.applySubstitution, recordedForm, StatementForm.applySubstitution,
      TypedBinder.applySubstitution, sameId]
    exact List.mem_singleton_self _
  have actualId : binder.id ∈ (Node.statement statement).definedLocalIds := by
    change binder.id ∈ statement.form.definedLocalIds
    rw [form]
    change binder.id ∈ initial.flatMap ForItemForm.definedLocalIds ++ post.flatMap ForItemForm.definedLocalIds
    rw [← List.flatMap_append]
    exact List.mem_flatMap.mpr ⟨.letDecl binder initializer, present, List.mem_singleton_self _⟩
  have same := same_node_of_defined unique recordedApplied (lookupStatement?_sound found).1 recordedId actualId
  have sameStatement := Node.statement.inj same
  have incompatible := congrArg StatementNode.form sameStatement
  simp only [StatementNode.applySubstitution, recordedForm, StatementForm.applySubstitution, form] at incompatible
  cases incompatible

private theorem item_binding_form
    {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {result : Ty} {reasonAt : ExpressionId → Word}
    {next : Scope → Except SourceCoreBasic.Error Expr} {finalScope : Scope} {finish : Expr}
    {fuel : Nat} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : AcceptedNamedBodyFlow.Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    ∀ selected ∈ tree.bindings, ∃ initializer, ForItemForm.letDecl selected.binder initializer ∈ items := by
  induction tree with
  | nil same accepted => intro selected member; cases member
  | absent projected remaining allocated ih =>
    intro selected member
    rcases List.mem_cons.mp member with head | tail
    · subst selected
      exact ⟨none, List.mem_cons_self⟩
    · obtain ⟨initializer, present⟩ := ih selected tail
      exact ⟨initializer, List.mem_cons_of_mem _ present⟩
  | initialized projected child generated childType remaining allocated ih =>
    intro selected member
    rcases List.mem_cons.mp member with head | tail
    · subst selected
      exact ⟨some _, List.mem_cons_self⟩
    · obtain ⟨initializer, present⟩ := ih selected tail
      exact ⟨initializer, List.mem_cons_of_mem _ present⟩
  | discard child generated remaining ih
  | assigning remaining accepted ih
  | assigned remaining receipt targetType ih
  | projectedAssigned remaining receipt route ih
  | bitNotting remaining accepted ih
  | bitNotted remaining receipt targetType ih
  | projectedBitNotted remaining receipt route ih =>
    intro selected member
    obtain ⟨initializer, present⟩ := ih selected member
    exact ⟨initializer, List.mem_cons_of_mem _ present⟩

/-- Every actual header binding receipt, including a suffix of either list,
inherits the result from its successful policy action and enclosing for node. -/
theorem Index.header_bindings_monomorphic
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    (index : Index compiled bodyRelation)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some compiled)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {id : StatementId} {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initial condition post body)
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : Scope → Except SourceCoreBasic.Error Expr} {finalScope : Scope} {finish : Expr}
    {fuel : Nat} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : AcceptedNamedBodyFlow.Items index.policy index.compilerSource site result reasonAt
      next finalScope finish fuel scope items code)
    (included : ∀ item ∈ items, item ∈ initial ++ post) :
    ∀ binding ∈ tree.bindings, binding.binder.scheme.quantified = [] := by
  intro binding member
  obtain ⟨initializer, present⟩ := item_binding_form tree binding member
  exact index.header_binder_monomorphic artifact checked found form (included _ present) binding.projected

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end
