import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed

/-! Existing compiler receipts exclude output coercions at their original node.
The raw-form shape receipt covers only the explicitly supported raw forms. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
open Frontend SourceInference Staging.Recursive

theorem empty_at {source : TypedSource} {id : ExpressionId} {node actual : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (empty : node.coercions = []) (contains : ContainsExpression source id actual) :
    actual.coercions = [] := by
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.coercions same).trans empty

theorem raw_shape {program : Program} {registry : Registry} {size : Nat} {invocation : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep}
    {outcome : Outcome}
    (trace : Size.RawForm program registry size invocation context environment before form requirements coercions outcome after) :
    AtomicForm form ∨ ∃ callee ids instantiation, form = .call callee ids (.declaration instantiation) := by
  cases trace with
  | rawAtomicValue atomic _ | rawAtomicFault atomic _ => exact .inl atomic
  | rawDirectArgumentsFault _ _ | rawDirectApplied _ _ _ _ _ => exact .inr ⟨_,_,_,rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
