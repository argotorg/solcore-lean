import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.SourceSemantics.SourceInferenceSubtreeInverseClosure

/-! Real lexical discovery stays inside the initializer's actual occurrence
subtree. A closed preserved earlier subtree then recovers complete records. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceInferenceSoundness

private theorem lexical_edge {source : TypedSource} {parent child : NodeId}
    (unique : NodeOccurrencesUnique source) (present : parent ∈ nodeIds source)
    (member : child ∈ localLambdaLexicalChildren source parent) :
    DirectChild source parent child := by
  obtain ⟨original, originalMember, originalId⟩ := List.mem_map.mp present
  obtain ⟨node, found, reference⟩ := localLambdaLexicalChildren_origin member
  have originalFound := lookupNode?_complete unique originalMember
    (congrArg NodeId.occurrenceId originalId)
  have same := Option.some.inj (found.symm.trans originalFound)
  subst node
  exact ⟨original, ⟨originalMember, originalId⟩, reference⟩

/-- The pruned lexical traversal uses actual source edges, including every
structured statement body that it visits. -/
theorem path_descends {source : TypedSource} {root node : NodeId} {roots : List NodeId}
    (unique : NodeOccurrencesUnique source) (closed : ChildEdgesExist source)
    (rootEdges : ∀ child ∈ roots, DirectChild source root child)
    (path : LocalLambdaLexicalPath source roots node) :
    Descends source root node ∧ node ∈ nodeIds source := by
  induction path with
  | root member =>
      have edge := rootEdges _ member
      obtain ⟨parent, contains, reference⟩ := edge
      exact ⟨.direct ⟨parent, contains, reference⟩, closed parent contains.1 _ reference⟩
  | child previous member ih =>
      have edge := lexical_edge unique ih.2 member
      obtain ⟨parent, contains, reference⟩ := edge
      exact ⟨ih.1.trans (.direct ⟨parent, contains, reference⟩),
        closed parent contains.1 _ reference⟩

/-- A complete record selected from this actual lambda body lies below the
same initializer identity used by the discovered instance. -/
theorem body_node_descends {source : TypedSource} {localInstance : LocalLambdaInstance}
    {nodes : List Node} {node : Node}
    (unique : NodeOccurrencesUnique source) (closed : ChildEdgesExist source)
    (accepted : localLambdaBodyNodes source localInstance = .ok nodes)
    (member : node ∈ nodes) :
    Descends source (.expression localInstance.binding.initializer) node.id := by
  obtain ⟨initializer, parameters, resultType, body, found, form, path⟩ :=
    localLambdaBodyNodes_path accepted member
  have contains := lookupExpression?_sound found
  apply (path_descends unique closed ?_ path).1
  intro child childMember
  refine ⟨.expression initializer, ⟨contains.1, congrArg NodeId.expression contains.2⟩, ?_⟩
  simpa only [nodeChildIds, Node.references, form, ExpressionForm.references] using childMember

/-- Earlier closure and genuine subtree preservation recover the complete
record, including a local read's exact binder target. -/
theorem body_node_before {before source : TypedSource} {localInstance : LocalLambdaInstance}
    {nodes : List Node} {node : Node}
    (unique : NodeOccurrencesUnique source) (sourceClosed : ChildEdgesExist source)
    (preserved : RawSubtreePreserved before source (.expression localInstance.binding.initializer))
    (beforeClosed : ChildEdgesExist before)
    (present : NodeId.expression localInstance.binding.initializer ∈ nodeIds before)
    (accepted : localLambdaBodyNodes source localInstance = .ok nodes) (member : node ∈ nodes) :
    node ∈ before.nodes :=
  preserved.node_inverse beforeClosed present unique (localLambdaBodyNodes_members accepted member)
    (.inr (body_node_descends unique sourceClosed accepted member))

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLexicalSubtree
