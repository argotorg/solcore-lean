import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.Frontend.SourceTypedRuntime

/-! An absent mapping entry whose value type has no default is a source fault.
The existing typed-source runtime represents this reason by a type mismatch
with no actual value type; that observation is preserved here. -/

set_option autoImplicit false

namespace Solcore.Test.SourceMappingDefaultFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def functionType : Ty := .function .word .word

/-- Non-defaultable mapping values remain admitted source types. -/
example (context : SourceSemantics.Context) :
    TypeWellScoped context [] (.mapping .word functionType) :=
  .mapping (.builtin .word) (.function (.builtin .word) (.builtin .word))

/-- Both successful evaluation prefixes contribute their heap effects before
missing-default failure; no result or failure of either child is invented. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before middle after : Heap)
    (id base index : ExpressionId) (node : ExpressionNode) (key : Core.Word)
    (contains : ContainsExpression source id node)
    (form_eq : node.form = .index base index)
    (layout : OrdinaryRequirementLayout node.requirements node.coercions [])
    (base_evaluates : ExpressionEvaluates program context evidence source
      environment before base (.mapping .word functionType []) middle)
    (index_evaluates : ExpressionEvaluates program context evidence source
      environment middle index (.word key) after) :
    ExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault (.missingMappingDefault functionType)) after := by
  apply ExpressionEvaluatesOutcome.fault
  apply ExpressionFaults.form contains
  rw [form_eq]
  exact .indexDefaultUnavailable layout base_evaluates index_evaluates
    (.word key) .nil (by intro defaultable; cases defaultable)

/-- No function is synthesized to fill an absent entry. -/
example (value : Value) : ¬ DefaultValue functionType value :=
  DefaultValue.not_function .word .word value

/-- The runtime's existing default calculation reports the same absence. -/
example : SourceTypedRuntime.defaultValue? (functionType.size + 1) functionType =
    none := by
  rfl

/-- Explicit runtime observation: `missingMappingDefault functionType` is
reported as `typeMismatch functionType none`. This also confirms the same
missing-default behavior on the runtime's projected-update path, before its
modifier can be invoked. Place-fault semantics remains a separate repair. -/
example (plan : SourceSpecializationWorklist.Plan) (key : Core.Word)
    (modify : Option SourceTypedRuntime.Value →
      Except SourceTypedRuntime.RuntimeError SourceTypedRuntime.Value) :
    SourceTypedRuntime.updateResolvedValue plan functionType modify
      (some (.mapping .word functionType [])) [.index (.word key)] =
      .error (.typeMismatch functionType none) := by
  rfl

end Solcore.Test.SourceMappingDefaultFault
