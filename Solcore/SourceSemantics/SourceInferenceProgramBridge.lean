import Solcore.SourceSemantics.SourceInferenceCheckedBodyTypingBridge
import Solcore.SourceSemantics.SourceStageAnalysisSoundness
import Solcore.SourceSemantics.Staging.Program

/-!
Assemble the one remaining recursive statement-inference theorem into the
whole-program declarative judgment.  The executable checker already provides
the headers, canonical signatures, and predicate fixity used below.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A closed recursive theorem for statement inference discharges the body
typing premise for every ordinary function and implementation method in the
same successful whole-program check. -/
theorem checkedProgramBodiesHaveStatementTyping_of_inferStatementsFuel_sound
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (recursiveSound : InferStatementsFuelSoundness fuel) :
    CheckedProgramBodiesHaveStatementTyping checked fuel := by
  constructor
  · intro function member signature signatureMember bodySuccess
    obtain ⟨headerSignature, headerMember, header⟩ :=
      checkedFunctionHeaderWellFormed_ofCheckProgram success member
    have signatureEq : headerSignature = signature := by
      have catalog := SignatureCatalogWellFormed.ofCheckProgram success
      have ids := catalog.function_ids
      have leftId : headerSignature.id = function.declaration :=
        header.declaration_eq.symm
      have rightId : function.declaration = signature.id :=
        checkFunctionBody_success_declaration bodySuccess
      exact eq_of_mem_of_nodup_map ids headerMember signatureMember
        (leftId.trans rightId)
    subst headerSignature
    have predicatesFixed :
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution function.substitution) =
            signature.scheme.predicates :=
      ((Frontend.checkProgram_success_signature_formation success).functions
        signature signatureMember).2.2.apply_eq_self function.substitution
    exact checkedBodyStatementsHaveType_ofCheckProgram_function success
      signatureMember header predicatesFixed bodySuccess recursiveSound
  · intro checkedMethod member implementation method trait
      implementationMember methodMember traitLookup bodySuccess
    let catalog := SignatureCatalogWellFormed.ofCheckProgram success
    have implementationWellFormed :=
      catalog.implementations_semantic implementation implementationMember
    have methodWellFormed :=
      implementationWellFormed.methods method methodMember
    obtain ⟨semanticTrait, traitMethod, semanticTraitMember,
      selectedHeadTrait, traitMethodMember, traitMethodId,
      _, _, _, _, _, _⟩ := methodWellFormed.trait_method
    have rawLookup :
        checked.signatures.traits.find?
          (fun candidate =>
            decide (candidate.id = method.traitMethod.trait)) =
              some trait := by
      simpa [ProgramSignatures.trait?] using traitLookup
    have selectedMember : trait ∈ checked.signatures.traits :=
      List.mem_of_find?_eq_some rawLookup
    have selectedId : trait.id = method.traitMethod.trait :=
      of_decide_eq_true (List.find?_some
        (p := fun candidate : ProgramTraitSignature =>
          decide (candidate.id = method.traitMethod.trait)) rawLookup)
    have semanticTraitWellFormed :=
      catalog.traits_semantic semanticTrait semanticTraitMember
    have traitMethodWellFormed :=
      semanticTraitWellFormed.methods traitMethod traitMethodMember
    have semanticId : semanticTrait.id = method.traitMethod.trait := by
      rw [← traitMethodWellFormed.owner]
      exact congrArg ProgramTraitMethodId.trait traitMethodId
    have traitEq : trait = semanticTrait :=
      Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids
        selectedMember semanticTraitMember (selectedId.trans semanticId.symm)
    subst semanticTrait
    let signature :=
      implementation.functionSignatureOfMethodWithTrait trait method
    have header : CheckedBodyHeaderWellFormed checked.signatures signature
        checkedMethod.checked :=
      CheckedBodyHeaderWellFormed.ofCheckImplementationMethod
        implementationWellFormed methodWellFormed bodySuccess
    have predicatesFixed :
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution
            checkedMethod.checked.substitution) =
          signature.scheme.predicates := by
      simpa [signature,
        ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
        ProgramImplementationSignature.functionSignatureOfMethod] using
        methodAssumptions_applySubstitution_eq_self catalog
          implementationMember methodMember selectedMember
          selectedHeadTrait checkedMethod.checked.substitution
    exact checkedBodyStatementsHaveType_ofCheckProgram_method success
      implementationMember header predicatesFixed bodySuccess recursiveSound

/-- The whole-program checker-to-`SourceSemantics` bridge has no remaining
header or per-declaration assumptions: its sole premise is the recursive
soundness theorem for the actual executable statement traversal. -/
theorem programWellFormed_ofCheckProgram_inferStatementsFuel_sound
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (recursiveSound : InferStatementsFuelSoundness fuel) :
    ProgramWellFormed (Program.ofChecked checked) :=
  Solcore.SourceSemantics.programWellFormed_ofCheckProgram_statements success
    (checkedProgramBodiesHaveStatementTyping_of_inferStatementsFuel_sound
      success recursiveSound)

end Solcore.SourceSemantics.SourceInferenceSoundness

namespace Solcore.SourceSemantics

open Frontend Frontend.SourceInference

/-- Every checked executable body has passed the executable staging traversal.
This is deliberately separate from static checking: stage analysis is a
distinct public compiler pass. -/
structure CheckedProgramStagesAnalyzed (checked : CheckedProgram) : Prop where
  functions : ∀ function, function ∈ checked.functions →
    ∃ analysis, Frontend.SourceStageAnalysis.analyzeFunction function = .ok analysis
  methods : ∀ method, method ∈ checked.methods →
    ∃ analysis, Frontend.SourceStageAnalysis.analyzeFunction method.checked =
      .ok analysis

/-- The successful stage traversal and the recursive source-checking proof
jointly admit the checked program to the independent whole-program staging
judgment.  No staging conclusion is inferred from static checking alone. -/
theorem programHasStages_ofCheckProgram_and_analysis
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (recursiveSound : SourceInferenceSoundness.InferStatementsFuelSoundness fuel)
    (analyzed : CheckedProgramStagesAnalyzed checked) :
    Staging.ProgramHasStages (Program.ofChecked checked) := by
  refine ⟨SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound
    success recursiveSound, ?_, ?_⟩
  · intro definition member
    obtain ⟨function, functionMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨analysis, stageSuccess⟩ := analyzed.functions function functionMember
    have valid := SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound
      success recursiveSound
    have functionValid := valid.functions_valid _ member
    cases functionValid with
    | intro _ _ bodyValid =>
        cases bodyValid with
        | intro _ _ _ _ _ _ _ _ _ _ graphClosed localIdentities _ _ _ _ =>
            exact (Staging.bodyDefinitionOfChecked_iff function).2
              (SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed
                function analysis graphClosed localIdentities stageSuccess)
  · intro definition member
    obtain ⟨method, methodMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨analysis, stageSuccess⟩ := analyzed.methods method methodMember
    have valid := SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound
      success recursiveSound
    have methodValid := valid.methods_valid _ member
    cases methodValid with
    | intro _ _ _ _ _ _ _ _ _ bodyValid =>
        cases bodyValid with
        | intro _ _ _ _ _ _ _ _ _ _ graphClosed localIdentities _ _ _ _ =>
            exact (Staging.bodyDefinitionOfChecked_iff method.checked).2
              (SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed
                method.checked analysis graphClosed localIdentities stageSuccess)

end Solcore.SourceSemantics
