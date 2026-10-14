import Solcore.SourceSemantics.SourceInferenceActualRootedContracts
import Solcore.SourceSemantics.SourceInferenceSelectedStatementState

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferForItemsFuelRootedSoundness_of_itemSoundness
    {fuel : Nat}
    (itemSound : ActualInferForItemFuelRootedSoundness fuel) :
    ActualInferForItemsFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn items
    initial result evidenceState roots finalized semanticSource
    frames semanticContext control success resources interfaces signaturesEq ownerEq
    parametersEq assumptionsEq signatureFormation functionsCanonical
    catalog signatureParameters initialInvariant actual operational returnAdmissible substitutionExtension
    resultExtension rawResultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    sourceOwner covered bindingsRetained actualCovered actualBindings
  induction items generalizing initial result semanticContext with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure]
        at success
      injection success with resultEq
      subst result
      exact ⟨semanticContext, initialInvariant, actual, operational,
        ForItemsHaveType.nil control semanticContext⟩
  | cons item rest induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemSuccess : Detail.inferForItemFuel fuel inferenceContext item
          initial with
      | error error =>
          simp [itemSuccess, bind, Except.bind] at success
      | ok itemPair =>
          rcases itemPair with ⟨inferredItem, itemState⟩
          simp only [itemSuccess, bind, Except.bind] at success
          cases tailSuccess : Detail.inferForItemsFuel fuel inferenceContext
              rest itemState with
          | error error =>
              simp [tailSuccess] at success
          | ok tail =>
              simp only [tailSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemProperties := Detail.inferForItemFuel_inferenceProperties
                initialInvariant.ready signatureFormation functionsCanonical
                itemSuccess
              have tailProperties := Detail.inferForItemsFuel_inferenceProperties
                itemProperties.2 signatureFormation functionsCanonical
                tailSuccess
              have itemSubstitutionExtension :
                  finalized.substitution.SemanticallyExtends
                    itemState.inference.substitution :=
                substitutionExtension.trans
                  tailProperties.1.substitution_extends
              have itemBelow : itemState.NodesBelowNextOccurrence :=
                (Detail.inferForItemFuel_occurrenceBoundExtends itemSuccess
                  ).nodesBelowNextOccurrence initialInvariant.nodesBelow
              have itemToResult : TypingSourceExtends
                  (itemState.toTypedSource roots)
                  (tail.state.toTypedSource roots) :=
                inferForItemsFuel_success_typingSourceExtends tailSuccess
                  itemBelow roots
              have itemExtension : ∀ reference ∈ inferredItem.references,
                  SubtreePreserved finalized.substitution (itemState.toTypedSource roots) semanticSource reference := by
                intro reference member
                exact (resultExtension inferredItem (by simp) reference member).monoBefore itemToResult
              have itemRawExtension : ∀ reference ∈ inferredItem.references,
                  RawSubtreePreserved (itemState.toTypedSource roots) (evidenceState.toTypedSource roots) reference := by
                intro reference member
                exact (rawResultExtension inferredItem (by simp) reference member).monoBefore itemToResult
              have itemPatternsSubset : itemState.integerPatterns ⊆
                  evidenceState.integerPatterns := by
                intro origin member
                exact integerPatternsSubset
                  ((Detail.inferForItemsFuel_integerPatterns_subset
                    tailSuccess) member)
              have itemLiteralsSubset : itemState.integerLiterals ⊆
                  evidenceState.integerLiterals := by
                intro origin member
                exact integerLiteralsSubset
                  ((Detail.inferForItemsFuel_integerLiterals_subset
                    tailSuccess) member)
              have itemRequirementsSubset : itemState.requirements ⊆
                  evidenceState.requirements := by
                intro requirement member
                exact requirementsSubset
                  ((Detail.inferForItemsFuel_requirements_subset
                    tailSuccess) member)
              have itemCovered : ForItemReferencesCovered
                  finalized.typedSource finalized.substitution
                  semanticContext inferredItem := by
                apply covered
                simp
              have itemBindingsRetained : ForItemBindingRetained
                  (evidenceState.toTypedSource roots) inferredItem := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inl member
              obtain ⟨middleContext, middleInvariant, middleActual, middleOperational, itemTyping⟩ :=
                itemSound itemSuccess resources interfaces signaturesEq ownerEq
                  parametersEq assumptionsEq signatureFormation
                  functionsCanonical catalog signatureParameters
                  initialInvariant actual operational returnAdmissible itemSubstitutionExtension itemExtension
                  itemRawExtension itemPatternsSubset
                  itemLiteralsSubset itemRequirementsSubset sourceOwner
                  itemCovered itemBindingsRetained
                  (actualCovered inferredItem (by simp)) (actualBindings inferredItem (by simp))
              have tailOwner : semanticSource.owner = itemState.owner :=
                sourceOwner.trans
                  (Detail.inferForItemFuel_preserves_owner itemSuccess).symm
              have tailCovered : ForItemsReferencesCovered
                  finalized.typedSource finalized.substitution middleContext
                  tail.items := by
                intro nextItem member
                have original : ForItemReferencesCovered
                    finalized.typedSource finalized.substitution
                    semanticContext nextItem := by
                  apply covered
                  simp [member]
                exact original.transportAssumptions
                  (forItemHasType_assumptions_eq itemTyping)
              have tailBindingsRetained : ForItemsBindingsRetained
                  (evidenceState.toTypedSource roots) tail.items := by
                intro binding member
                apply bindingsRetained
                simp only [List.flatMap_cons, List.mem_append]
                exact Or.inr member
              have fields := forItemHasType_nonlocal_fields_eq itemTyping
              have middleReturn : TypeAdmissible middleContext (finalized.substitution.apply expectedReturn) :=
                StructuralSubstitution.TypeAdmissible.transportContext fields.1 fields.2.1 fields.2.2.1
                  (middleActual.variables_eq.trans actual.variables_eq.symm) fields.2.2.2.1 returnAdmissible
              obtain ⟨finalContext, finalInvariant, finalActual, finalOperational, tailTyping⟩ :=
                induction (initial := itemState) (result := tail)
                  (semanticContext := middleContext) tailSuccess
                  middleInvariant middleActual middleOperational middleReturn substitutionExtension
                  (fun next member => resultExtension next (by simp [member]))
                  (fun next member => rawResultExtension next (by simp [member]))
                  integerPatternsSubset integerLiteralsSubset
                  requirementsSubset tailOwner tailCovered
                  tailBindingsRetained
                  (fun next member => actualCovered next (by simp [member]))
                  (fun next member => actualBindings next (by simp [member]))
              refine ⟨finalContext, finalInvariant, finalActual, finalOperational, ?_⟩
              exact ForItemsHaveType.cons itemTyping tailTyping

end Solcore.SourceSemantics.SourceInferenceSoundness
