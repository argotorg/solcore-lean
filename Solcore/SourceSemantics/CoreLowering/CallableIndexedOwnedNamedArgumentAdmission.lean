import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Genuine direct-call typing and the actual successful argument trace supply
raw Source admission for the named callee. The original argument type row stays
independent of projected native types; packed typing is unpacked only after the
actual argument arity is known. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedCatalog CallableAncestryPairedLookup

/-- The actual direct-call parent exposes the original raw argument row and
its complete declaration application. -/
theorem direct_arguments {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {node : ExpressionNode}
    {type : TypeSystem.Ty} {instantiation : DeclarationInstantiation}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (typed : ExpressionHasType source context id type) :
    ∃ originalTypes rawResult predicates,
      ExpressionsHaveTypes source context ids originalTypes ∧
      SourceSemantics.DeclarationApplicationValid context instantiation originalTypes rawResult predicates := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    rw [form] at raw
    cases raw with
    | directCall _ application arguments => exact ⟨_, _, _, arguments, application⟩

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- Original argument execution supplies the actual heap; the genuine Header
certificate supplies the callee context and raw binder types. -/
theorem at_successful_arguments (header : Header prepared values definitions program)
    {context : SourceSemantics.Context} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {ids : List ExpressionId} {arguments : List Dynamic.Value} {originalTypes : List TypeSystem.Ty}
    {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
    (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
    (evaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before ids arguments after)
    (arity : header.function.parameters.length = arguments.length) :
    Dynamic.HeapWellTyped header.function.context after ∧
      Dynamic.ValuesHaveTypes header.function.context after arguments header.types := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type runtime covers locals heapTyped typed evaluated
  have actual := Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped argumentTypes evaluated
  obtain ⟨facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  cases application with
  | intro _signature _valid _declaration _parameters _result functionType _predicates =>
    have packedType := (TypeSystem.Ty.function.inj (functionType.symm.trans certified.callable_type)).1
    obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
    have packedTyped := packing.hasType actual.1
    rw [packedType] at packedTyped
    have signatures := certified.signatures_eq.trans runtime.signatures.symm
    have bodyHeap := actual.2.1.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have bodyPacked := packedTyped.transportClosed signatures runtime.closed certified.type_parameters_empty
      runtime.variables_closed certified.residual_type_variables_open
    have length : arguments.length = header.types.length :=
      arity.symm.trans ((congrArg List.length header.frame.parameters).trans certified.typing.inputs_extend.length_eq)
    have bodyArguments := packing.unpackTypes bodyPacked length
    exact ⟨header.frame.context.symm ▸ bodyHeap, header.frame.context.symm ▸ bodyArguments⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedArgumentAdmission
