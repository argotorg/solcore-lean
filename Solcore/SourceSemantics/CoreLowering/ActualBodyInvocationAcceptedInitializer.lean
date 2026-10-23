import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationInitializerReceipt
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows

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
