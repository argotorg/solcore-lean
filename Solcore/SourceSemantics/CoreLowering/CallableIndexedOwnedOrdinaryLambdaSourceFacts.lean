import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

/-! The actual Source lambda judgment supplies the raw function type and body
receipt at the same occurrence. Authentic Source runtime fields and evidence
then construct its closure frame, independently of native callable typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
open Core Frontend SourceInference

/-- All fields refer to the original Source row and the literal closure. -/
structure Facts (function : Dynamic.Closure) (id : ExpressionId) (node : ExpressionNode) : Prop where
  contains : ContainsExpression function.source id node
  form : node.form = .lambda function.parameters function.resultType function.body
  rawType : node.rawType = FunctionValues.sourceType function
  sourceType : node.type = FunctionValues.sourceType function
  ordinary : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []
  coercions : node.coercions = []
  typing : ExpressionFormHasRawType function.source function.context node.form
    (FunctionValues.sourceType function) (.ordinary [])

variable {function : Dynamic.Closure} {id : ExpressionId} {node : ExpressionNode}

/-- One lookup and typing inversion retains the complete original body
judgment. Parameter packing comes from the actual monomorphic binder row. -/
theorem of_typed (unique : NodeOccurrencesUnique function.source)
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body)
    (typed : ExpressionHasType function.source function.context id node.type)
    (coercions : node.coercions = []) : Facts function id node := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actual raw plan contains formTyped rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at formTyped
    cases formTyped with
    | @lambda _ lambdaContext finalContext _ parameterTypes _ _ bodyFacts namesUnique parametersExtend bodyTyped completes =>
      have bodies := MonoBindersExtend.bodyTypes_eq parametersExtend
      have shape : TypeSystem.Ty.function (TypeSystem.Ty.productMany parameterTypes) function.resultType =
          FunctionValues.sourceType function := by
        simp only [FunctionValues.sourceType, bodies]
      have finalType : node.type = FunctionValues.sourceType function := by
        simpa only [ExpressionNode.rawType, coercions] using rawType.trans shape
      cases requirements with
      | ordinary owned path layout =>
        refine ⟨contains, form, rawType.trans shape, finalType, layout, coercions, ?_⟩
        rw [form, ← shape]
        exact .lambda namesUnique parametersExtend bodyTyped completes

/-- The same actual static Source validity supplies every closure-code field.
No body execution or native-code equality is used to construct the frame. -/
theorem Facts.frame (facts : Facts function id node) {program : Program}
    (runtime : Dynamic.SourceRuntimeValid program function.context function.source)
    (covers : function.evidence.Covers function.context) : Dynamic.ClosureFrame program function := by
  refine ⟨runtime.signatures, runtime.owner, ?_, runtime.requirements.idsUnique, covers⟩
  exact {
    owner := runtime.owner
    closed := runtime.closed
    variables_closed := runtime.variables_closed
    residual_variables_open := runtime.residual_variables_open
    graph := runtime.graph
    requirement_ledger := runtime.requirements
    occurrence := ⟨id, node, facts.contains, facts.form, facts.rawType, facts.typing⟩ }

section ActualProduced
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- The chosen compiler Site already keeps the original lookup and form.
Genuine Source typing supplies its raw fields at that same occurrence. -/
theorem Produced.source_facts
    (unique : NodeOccurrencesUnique (source caller.named))
    (typed : ExpressionHasType (source caller.named) sourceContext id produced.site.code.sourceNode.type)
    (coercions : produced.site.code.sourceNode.coercions = []) :
    Facts (closure caller.named parameters result statements sourceContext evidence []) id produced.site.code.sourceNode := by
  have found : (source caller.named).lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier] using produced.site.code.sourceFound
  exact of_typed unique found produced.site.code.sourceForm typed coercions

/-- This derives the genuine frame needed by the static joint-body collector.
Its whole Source runtime receipt and covering evidence remain explicit. -/
theorem Produced.frame_of_typed
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (typed : ExpressionHasType (source caller.named) sourceContext id produced.site.code.sourceNode.type)
    (coercions : produced.site.code.sourceNode.coercions = []) :
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure caller.named parameters result statements sourceContext evidence []) :=
  (Produced.source_facts caller produced runtime.graph.nodeOccurrencesUnique typed coercions).frame runtime covers

end ActualProduced
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
