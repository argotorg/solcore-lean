import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues

/-! Authenticate the callable hooks used by the actual general compiler.
These are static code equations. Source code/capture typing and the body
meaning theorem remain separate obligations. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy

open Frontend Frontend.SourceInference

private theorem descriptor_reconstructs
    {table : SourceCoreStageCodebook.Table} {origin : SourceCoreStageCodebook.Origin}
    (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    SourceCoreCallableContracts.descriptor table origin = .ok descriptor := by
  cases descriptor
  rename_i id found
  unfold SourceCoreCallableContracts.descriptor
  split
  · rename_i missing
    rw [found] at missing
    contradiction
  · rename_i selected actual
    have same := Option.some.inj (actual.symm.trans found)
    subst selected
    rfl

/-- Lambda decoration in the production policy uses the exact full
instantiation context recorded in the artifact's sealed codebook. -/
theorem lambda_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (id : ExpressionId) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.lambda context.owner id active)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.lambda id) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem named_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (key : SourceCoreStageCodebook.Key) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named key)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.named key) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem builtin_decoration
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (function : BuiltinFunctionId) (parameter result : Core.Ty) (value : Core.Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).decorateCallable
      context source node (.builtin function) parameter result (Core.LanguageResult.success value) =
      .ok (Core.LanguageResult.success (descriptor.wrap value)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, descriptor_reconstructs descriptor,
    Core.LanguageResult.success, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem indirect_call
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (context : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : IndirectCallResolution)
    (result : Core.Ty) (calleeCode argumentsCode : Core.Expr)
    (site : SourceCoreCallableContracts.Callsite)
    (form : node.form = .call callee arguments (.indirect function))
    (accepted : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      context source node result calleeCode argumentsCode =
      .ok (site.lower native.diagnostics.unknown result calleeCode argumentsCode) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form, accepted,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The real policy supplies the decoration obligation of the generic
contracted closure certificate. No source or Core execution is assumed. -/
def closureCode
    {catalog : SourceCoreDataCatalog.Catalog} {program : Program}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {active : TypeSystem.Substitution}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {id : ExpressionId} {node : ExpressionNode}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation function.source
      scope id node function.parameters function.resultType function.body reportedType lowered)
    (owner : compilation.owner.declaration = function.source.owner)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.lambda compilation.owner id active))
    (frame : Dynamic.ClosureFrame program function)
    (projection : catalog.project (FunctionValues.sourceType function) = .ok
      (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore))
    (typed : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      lowered.expression (Core.LanguageResult.resultType
        (Core.CallableContract.functionType artifact.raw.parameterCore artifact.raw.resultCore)) catalog.definitions) :
    ContractedFunctionValues.Code catalog program bodyCertificate policy compilation native.table active
      function scope administrativeContext where
  id := id
  node := node
  reportedType := reportedType
  lowered := lowered
  artifact := artifact
  owner := owner
  descriptor := descriptor
  decoration := by
    intro value
    rw [profile]
    exact lambda_decoration native active compilation function.source node id
      artifact.raw.parameterCore artifact.raw.resultCore value descriptor
  frame := frame
  projection := projection
  outputTyped := typed

end Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
