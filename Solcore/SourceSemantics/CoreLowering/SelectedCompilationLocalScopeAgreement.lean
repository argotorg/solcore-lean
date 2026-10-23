import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement

/-! Compatibility body views are projections of the actual complete node agreement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
open CallableLambdaBodyReachability CallableBodyMetadataViews

/-- A concrete caller allocated after this target cannot change the target's
own or nested quantifiers. Captured ancestors agree by the actual saved-context
extension. The conclusion compares only this exact lambda's reached initializer and body. -/
theorem body_view_at_later_caller
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    (before : target.binding.binder.id.binderIndex < caller.binding.binder.id.binderIndex)
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    BodyView (named.specialized.function.typedBody.applySubstitution lexical)
      (named.specialized.function.typedBody.applySubstitution caller.substitution)
      (lambdaRoots target.binding.initializer body) :=
  GeneralizedLocalResidualAgreement.body_view_of_nodes
    (SelectedCompilationLocalNodeAgreement.nodes_at_later_caller selected artifact checked
      position row callerOrigin targetOrigin before extension captured found form)

/-- The exact local read supplies the ordering used above. The saved-context
extension alone is never treated as a noninterference law. -/
theorem body_view_at_local_read
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    {read : ExpressionNode} {name : String}
    (readMember : Node.expression read ∈ named.specialized.function.typedBody.nodes)
    (readPath : Descends named.specialized.function.typedBody
      (.expression caller.binding.initializer) (.expression read.id))
    (readForm : read.form = .reference name (.local target.binding.binder.id))
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    BodyView (named.specialized.function.typedBody.applySubstitution lexical)
      (named.specialized.function.typedBody.applySubstitution caller.substitution)
      (lambdaRoots target.binding.initializer body) :=
  GeneralizedLocalResidualAgreement.body_view_of_nodes
    (SelectedCompilationLocalNodeAgreement.nodes_at_local_read selected artifact checked
      position row callerOrigin targetOrigin readMember readPath readForm extension captured found form)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
