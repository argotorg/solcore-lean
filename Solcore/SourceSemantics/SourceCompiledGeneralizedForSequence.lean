import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

theorem forItemsRooted_of_item_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (itemSound : ForItemRootedSoundnessFor callProvenance selected childFuel) :
    ForItemsRootedSoundnessFor callProvenance selected childFuel := by
  intro inferenceContext items expectedReturn initial result frames target here boundary
  induction items generalizing initial result target with
  | nil =>
      have success := boundary.accepted
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure] at success
      cases Except.ok.inj success
      exact ⟨target, boundary.invariant, boundary.actual, boundary.operational, .nil _ _⟩
  | cons item rest induction =>
      have success := boundary.accepted
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel childFuel inferenceContext item initial with
      | error error => simp [itemSuccess, bind, Except.bind] at success
      | ok pair =>
          obtain ⟨inferredItem, itemState⟩ := pair
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel childFuel inferenceContext rest itemState with
          | error error => simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              cases Except.ok.inj success
              have itemProperties := Detail.inferForItemFuel_inferenceProperties boundary.invariant.ready
                (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) itemSuccess
              have tailProperties := Detail.inferForItemsFuel_inferenceProperties itemProperties.2
                (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked) tailSuccess
              have itemBelow := (Detail.inferForItemFuel_occurrenceBoundExtends itemSuccess
                ).nodesBelowNextOccurrence boundary.invariant.nodesBelow
              have itemToTail := inferForItemsFuel_success_typingSourceExtends tailSuccess itemBelow (bodyRoots selected)
              obtain ⟨middle, middleInvariant, middleActual, middleOperational, itemTyped⟩ :=
                itemSound (descend here (.forItems_head boundary.accepted itemSuccess)) ({
                  accepted := itemSuccess
                  interfaces := boundary.interfaces
                  extension := boundary.extension.trans tailProperties.1.substitution_extends
                  scope := boundary.scope
                  invariant := boundary.invariant
                  actual := boundary.actual
                  operational := boundary.operational
                  rawReferences := fun reference member =>
                    (boundary.rawReferences inferredItem (by simp) reference member).monoBefore itemToTail
                  integerPatterns := (Detail.inferForItemsFuel_integerPatterns_subset tailSuccess).trans boundary.integerPatterns
                  integerLiterals := (Detail.inferForItemsFuel_integerLiterals_subset tailSuccess).trans boundary.integerLiterals
                  requirements := (Detail.inferForItemsFuel_requirements_subset tailSuccess).trans boundary.requirements
                  owner := boundary.owner
                  covered := boundary.covered inferredItem (by simp)
                  bindingsRetained := by
                    intro binding member
                    apply boundary.bindingsRetained
                    simp only [List.flatMap_cons, List.mem_append]
                    exact .inl member
                  actualCovered := boundary.actualCovered inferredItem (by simp)
                  actualBindings := boundary.actualBindings inferredItem (by simp)
                } : ForItemBoundary selected childFuel inferenceContext item expectedReturn
                  initial inferredItem itemState frames target)
              obtain ⟨finalContext, invariant, actual, operational, tailTyped⟩ :=
                induction (descend here (.forItems_tail boundary.accepted itemSuccess tailSuccess)) ({
                  accepted := tailSuccess
                  interfaces := boundary.interfaces
                  extension := boundary.extension
                  scope := boundary.scope
                  invariant := middleInvariant
                  actual := middleActual
                  operational := middleOperational
                  rawReferences := fun next member => boundary.rawReferences next (by simp [member])
                  integerPatterns := boundary.integerPatterns
                  integerLiterals := boundary.integerLiterals
                  requirements := boundary.requirements
                  owner := boundary.owner.trans (Detail.inferForItemFuel_preserves_owner itemSuccess).symm
                  covered := fun next member => (boundary.covered next (by simp [member])).transportAssumptions
                    (forItemHasType_assumptions_eq itemTyped)
                  bindingsRetained := by
                    intro binding member
                    apply boundary.bindingsRetained
                    simp only [List.flatMap_cons, List.mem_append]
                    exact .inr member
                  actualCovered := fun next member => boundary.actualCovered next (by simp [member])
                  actualBindings := fun next member => boundary.actualBindings next (by simp [member])
                } : ForItemsBoundary selected childFuel inferenceContext rest expectedReturn itemState tail frames middle)
              exact ⟨finalContext, invariant, actual, operational, .cons itemTyped tailTyped⟩

theorem forItemsRooted_of_item
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (itemSound : ForItemRootedSoundness selected childFuel) :
    ForItemsRootedSoundness selected childFuel := by
  exact forItemsRooted_of_item_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => itemSound boundary) True.intro

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
