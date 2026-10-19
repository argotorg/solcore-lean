import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation

/-! Finite source observations for an ordinary local read in a generalized
instance body. The original catalog and full specialization key are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
open Core Frontend SourceInference

structure Observations (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  name : String
  binder : Resolved.LocalId
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.local binder)
  requirements : node.requirements = []
  coercions : node.coercions = []
  notInitializer : locals.bindings.find? (fun binding =>
    decide (binding.caller = owner ∧ binding.initializer = id)) = none
  ordinary : locals.bindings.any (fun binding =>
    decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

def observations? (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) : Option (Observations locals owner source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node => match form : node.form with
    | .reference name (.local binder) =>
      if requirements : node.requirements = [] then
        if coercions : node.coercions = [] then
          if notInitializer : locals.bindings.find? (fun binding =>
              decide (binding.caller = owner ∧ binding.initializer = id)) = none then
            if ordinary : locals.bindings.any (fun binding =>
                decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
              some ⟨node, name, binder, found, form, requirements, coercions, notInitializer, ordinary⟩
            else none
          else none
        else none
      else none
    | _ => none

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
