import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
import Solcore.SourceSemantics.CoreLowering.CellAwareSelectedReadBounds

/-! A genuinely retained generalized cell excludes ordinary reads at that
same location. Original requirement evidence closes the selected dictionary;
empty output coercions leave the source heap and materialized value intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
open Core Frontend SourceInference TypeSystem GeneralHeap

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
  {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
  {size : Nat} {outcome : Staging.Recursive.Outcome}

theorem raw_type
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (coercions : node.coercions = [])
    (typed : ExpressionHasType invocation.source context id node.type) : node.rawType = node.type := by
  generalize result : node.type = type at typed
  cases typed with
  | intro contains _ raw _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    exact raw

theorem invert
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location cell) (descriptor : cell.generalized = some function)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id outcome after) :
    ∃ owned substitution produced,
      Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence function.binder node.rawType
        owned substitution produced ∧
      outcome = .value (.closure (function.instantiate substitution
        (produced ++ invocation.evidence.applySubstitution substitution))) ∧ after = before := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have ordinary_false : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell.generalized = none → False := by
    intro otherLocation otherCell otherLookup otherRead empty
    cases same_cell otherLookup otherRead
    rw [descriptor] at empty
    cases empty
  cases outcome with
  | value value =>
    have plain := trace.sound.value_plain
    cases plain with
    | intro contains raw path =>
      cases same_node contains
      rw [form] at raw
      cases raw with
      | «local» _ otherLookup otherRead empty _
      | localEmptyMapping _ otherLookup otherRead empty _ _ _ =>
        exact False.elim (ordinary_false otherLookup otherRead empty)
    | generalizedLocal contains otherForm _ otherLookup otherRead otherDescriptor _ instantiation path =>
      cases same_node contains
      rw [form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      have sameFunction := Option.some.inj (otherDescriptor.symm.trans descriptor)
      cases sameFunction
      rw [coercions] at path
      cases path
      exact ⟨_, _, _, instantiation, rfl, rfl⟩
  | fault failure =>
    cases failure with
    | stage failedScope call reason =>
      exact False.elim (CellAwareSelectedReadBounds.no_stage unique found form coercions trace)
    | semantic reason =>
      have plain := trace.sound.semanticFault_plain
      cases plain with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains raw =>
        cases same_node contains
        rw [form] at raw
        cases raw with
        | localUnbound _ unbound => exact False.elim (unbound.excludes_lookup lookup)
        | localDangling _ otherLookup dangling =>
          cases otherLookup.functional lookup
          exact False.elim (dangling.excludes_read read)
        | localUninitialized _ otherLookup otherRead empty _ _ =>
          exact False.elim (ordinary_false otherLookup otherRead empty)
      | coercion contains _ failed =>
        cases same_node contains
        rw [coercions] at failed
        cases failed
      | generalizedLocalRequirement _ _ _ _ _ _ _ selection failed =>
        obtain ⟨produced, producedOk⟩ := Dynamic.RequirementSequenceProves.produces_of_covers covers selection.requirements
        exact False.elim (producedOk.excludes_fault requirementsUnique failed)
      | generalizedLocalCoercion contains _ _ _ _ _ _ _ failed =>
        cases same_node contains
        rw [coercions] at failed
        cases failed

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
