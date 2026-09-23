import Solcore.SourceSemantics.Dynamic.ProgramPreservation

/-!
Focused construction tests for whole-program declarative admission.

The empty catalog is deliberately small, but it exercises every top-level
coverage and uniqueness field without relying on the executable frontend.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsProgram

open Frontend
open SourceSemantics
open TypeSystem
open SourceSemantics.Dynamic

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
}

private def emptyProgram : SourceSemantics.Program := {
  signatures := emptySignatures
  functions := []
  methods := []
}

theorem emptySignatureCatalogWellFormed :
    SignatureCatalogWellFormed emptySignatures := by
  constructor <;> simp [emptySignatures, signatureDeclarationIds]

theorem emptyProgramWellFormed : ProgramWellFormed emptyProgram := by
  refine {
    signatures := emptySignatureCatalogWellFormed
    function_ids := ?_
    method_ids := ?_
    functions_valid := ?_
    methods_valid := ?_
    functions_complete := ?_
    methods_complete := ?_
  } <;> simp [emptyProgram, emptySignatures]

theorem emptyProgramHasStages :
    SourceSemantics.Staging.ProgramHasStages emptyProgram := {
  staticallyValid := emptyProgramWellFormed
  functions := by simp [emptyProgram]
  methods := by simp [emptyProgram]
}

private def unitModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"source_semantics_program", by decide⟩], by decide⟩⟩

private def unitOwner : Resolved.DeclarationId := ⟨unitModule, 0⟩

private def unitSourceId : Syntax.SourceId := {
  origin := .main
  path := "source_semantics_program.sol"
}

private def unitSpan : Syntax.SourceSpan := {
  source := unitSourceId
  startByte := 0
  endByte := 0
}

/-- The parsed declaration is retained only as source metadata by the resolved
signature; the declarative semantic body below remains independently forgeable. -/
private def unitSyntax : Syntax.FunctionDecl := {
  span := unitSpan
  value := {
    signature := {
      span := unitSpan
      name := ⟨unitSpan, "unitMain"⟩
      genericParameters := none
      parameters := ⟨unitSpan, []⟩
      modifiers := ⟨none, none⟩
      returnsClause := none
      whereClause := none
    }
    body := ⟨unitSpan, []⟩
  }
}

private def unitSignature : ProgramFunctionSignature := {
  id := unitOwner
  name := "unitMain"
  parameters := []
  returnTypes := []
  returnComptime := false
  scheme := {
    parameters := []
    predicates := []
    body := .function .unit .unit
  }
  source := unitSyntax
}

private def unitSignatures : ProgramSignatures := {
  functions := [unitSignature]
  implRules := []
  traits := []
  implementations := []
  dataTypes := []
}

private def unitSource : Frontend.SourceInference.TypedSource := {
  owner := unitOwner
  inputs := []
  roots := []
  nodes := []
}

private def unitBody : BodyDefinition := {
  owner := unitOwner
  type := .function .unit .unit
  resultType := .unit
  returnComptime := false
  solvedRequirements := []
  source := unitSource
}

private def unitProgram : SourceSemantics.Program := {
  signatures := unitSignatures
  functions := [{ body := unitBody }]
  methods := []
}

theorem unitSignatureCatalogWellFormed :
    SignatureCatalogWellFormed unitSignatures := by
  refine {
    impl_rules_eq := by rfl
    declaration_ids := by
      simp [unitSignatures, signatureDeclarationIds, unitSignature]
    function_ids := by simp [unitSignatures, unitSignature]
    data_ids := by simp [unitSignatures]
    trait_ids := by simp [unitSignatures]
    implementation_ids := by simp [unitSignatures]
    constructor_ids := by simp [unitSignatures]
    trait_method_ids := by simp [unitSignatures]
    implementation_method_ids := by simp [unitSignatures]
    function_parameters := by simp [unitSignatures, unitSignature]
    data_parameters := by simp [unitSignatures]
    trait_parameters := by simp [unitSignatures]
    implementation_parameters := by simp [unitSignatures]
    functions_semantic := ?_
    data_semantic := by simp [unitSignatures]
    traits_semantic := by simp [unitSignatures]
    implementations_semantic := by simp [unitSignatures]
  }
  intro signature member
  simp only [unitSignatures, List.mem_singleton] at member
  subst signature
  refine {
    parameters_nodup := by simp [unitSignature]
    parameters_owned := by simp [unitSignature]
    parameter_positions := by
      intro index
      exact Fin.elim0 index
    parameter_names_nodup := by
      simp [ProgramFunctionSignature.parameterNames, unitSignature]
    parameter_types := by
      simp [TypesWellFormed, ProgramFunctionSignature.parameterTypes,
        unitSignature]
    return_types := by simp [TypesWellFormed, unitSignature]
    predicates := by simp [PredicatesWellFormed, unitSignature]
    scheme_body := by rfl
  }

theorem unitOccurrenceGraphClosed : OccurrenceGraphClosed unitSource := by
  refine {
    wellFormed := ?_
    rootsUnique := by simp [RootsUnique, unitSource]
    childSlotsUnique := by simp [ChildSlotsUnique, unitSource]
    childHasUniqueParent := by
      intro left right child leftEdge _
      rcases leftEdge with ⟨node, contains, _⟩
      simp [ContainsNode, unitSource] at contains
    rootsHaveNoParent := by simp [RootsHaveNoParent, unitSource]
    allNodesReachable := by simp [AllNodesReachable, unitSource]
    acyclic := by
      intro id descends
      cases descends with
      | direct edge =>
          rcases edge with ⟨node, contains, _⟩
          simp [ContainsNode, unitSource] at contains
      | step edge _ =>
          rcases edge with ⟨node, contains, _⟩
          simp [ContainsNode, unitSource] at contains
  }
  refine {
    nodeOccurrencesUnique := by simp [NodeOccurrencesUnique, nodeOccurrenceIds,
      unitSource]
    nodesOwned := by simp [NodesOwned, unitSource]
    rootsOwned := by simp [RootsOwned, unitSource]
    rootsExist := by simp [RootsExist, unitSource]
    childEdgesExist := by simp [ChildEdgesExist, unitSource]
  }

theorem unitLocalIdentityOwnership : LocalIdentityOwnership unitSource := by
  constructor <;> simp [definedLocalIds, unitSource]

theorem unitBodyHasType :
    BodyDefinitionHasType unitSignatures [] [] [] [] [] [] false unitBody
      .empty := by
  apply BodyDefinitionHasType.intro
      (lexicalContext := declarationContext unitSignatures unitOwner [] [] [])
  · rfl
  · simp [TypeParameterBindersWellFormed, declarationContext,
      Context.withSolvedRequirements, Context.withAssumptions,
      Context.withResidualTypeVariables, Context.forDeclaration,
      Context.ofSignatures]
  · simp [TypesWellFormed]
  · simp [TypesWellFormed]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .nil _
  · exact unitOccurrenceGraphClosed
  · exact unitLocalIdentityOwnership
  · constructor
    · simp [RequirementIdsUnique, unitBody, declarationContext,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.withResidualTypeVariables, Context.forDeclaration,
        Context.ofSignatures]
    · intro requirement member
      simp [unitBody, declarationContext, Context.withSolvedRequirements,
        Context.withAssumptions, Context.withResidualTypeVariables,
        Context.forDeclaration,
        Context.ofSignatures] at member
  · constructor <;>
      simp [primaryRequirementIds, unitBody, unitSource, declarationContext,
        Context.withSolvedRequirements, Context.withAssumptions,
        Context.withResidualTypeVariables, Context.forDeclaration,
        Context.ofSignatures]
  · refine ⟨_, .nil _ _, ?_, ?_⟩
    · intro expression member
      simp [unitBody, unitSource] at member
    · simp [BodyCompletes, BodyFacts.empty, ControlSummary.ordinary,
        TypeSystem.Ty.productMany]
  · rfl

theorem unitFunctionValid :
    FunctionDefinition.Valid unitSignatures { body := unitBody } := by
  apply FunctionDefinition.Valid.intro (signature := unitSignature)
      (facts := .empty)
  · simp [unitSignatures]
  · rfl
  · exact unitBodyHasType

theorem unitProgramWellFormed : ProgramWellFormed unitProgram := by
  refine {
    signatures := unitSignatureCatalogWellFormed
    function_ids := by simp [unitProgram, unitBody]
    method_ids := by simp [unitProgram]
    functions_valid := ?_
    methods_valid := by simp [unitProgram]
    functions_complete := ?_
    methods_complete := by simp [unitProgram, unitSignatures]
  }
  · intro definition member
    simp only [unitProgram, List.mem_singleton] at member
    subst definition
    exact unitFunctionValid
  · intro signature signatureMember
    simp only [unitProgram, unitSignatures, List.mem_singleton] at signatureMember
    subst signature
    exact ⟨{ body := unitBody }, by simp [unitProgram], rfl⟩

theorem unitBodyHasStages :
    SourceSemantics.Staging.BodyDefinitionHasStages unitBody := by
  apply SourceSemantics.Staging.BodyDefinitionHasStages.intro
      (inputScope := []) (finalScope := [])
  · rfl
  · exact unitOccurrenceGraphClosed
  · exact unitLocalIdentityOwnership
  · apply SourceSemantics.Staging.FunctionInputsStage.ordinary
    · rfl
    · intro comptimeOnly
      cases comptimeOnly
    · exact .nil []
  · exact .nil []

theorem unitProgramHasStages :
    SourceSemantics.Staging.ProgramHasStages unitProgram := by
  refine {
    staticallyValid := unitProgramWellFormed
    functions := ?_
    methods := by simp [unitProgram]
  }
  intro definition member
  simp only [unitProgram, List.mem_singleton] at member
  subst definition
  exact unitBodyHasStages

private def unitInstantiation :
    Frontend.SourceInference.DeclarationInstantiation := {
  declaration := unitOwner
  parameterSubstitution := []
  type := .function .unit .unit
  predicates := []
  parameterComptime := []
  returnComptime := false
}

private def unitBodyInstance : BodyInstance := {
  context := declarationContext unitSignatures unitOwner [] [] []
  source := unitSource
  resultType := .unit
}

private def unitEntry : ProgramEntry := {
  instantiation := unitInstantiation
  evidence := []
  arguments := []
}

theorem unitInstantiationValid :
    SourceSemantics.DeclarationInstantiation.Valid
      (Context.ofSignatures unitSignatures) unitInstantiation := by
  apply SourceSemantics.DeclarationInstantiation.Valid.intro unitSignature
  · change unitSignature ∈ [unitSignature]
    simp
  · rfl
  · exact SourceSemantics.ParameterSubstitution.exact_empty
  · intro parameter replacement member
    change (parameter, replacement) ∈
      ([] : TypeSystem.ParameterSubstitution) at member
    simp at member
  · rfl
  · rfl
  · rfl
  · rfl

theorem unitFunctionInstantiates :
    FunctionInstantiates unitProgram unitInstantiation unitBodyInstance := by
  apply FunctionInstantiates.intro
      (signature := unitSignature) (definition := { body := unitBody })
  · simp [unitProgram, unitSignatures]
  · simp [unitProgram]
  · rfl
  · rfl
  · exact unitInstantiationValid
  · rfl
  · rfl
  · rfl

theorem unitEvidenceCovers :
    EvidenceEnvironment.Covers unitBodyInstance.context [] := by
  constructor
  · intro goal evidence lookup
    cases lookup
  · intro predicate member
    simp [unitBodyInstance, declarationContext, Context.withSolvedRequirements,
      Context.withAssumptions, Context.withResidualTypeVariables,
      Context.forDeclaration, Context.ofSignatures]
      at member

theorem emptyHeapWellTyped :
    HeapWellTyped unitBodyInstance.context ⟨[]⟩ := by
  intro cell member
  simp at member

theorem unitEntryValid :
    ProgramEntryValid unitProgram unitEntry ⟨[]⟩ unitBodyInstance := {
  instantiates := unitFunctionInstantiates
  evidence_covers := unitEvidenceCovers
  heap_typed := emptyHeapWellTyped
  arguments_typed := .nil
}

theorem unitBodyInvokes :
    BodyInvokes unitProgram unitBodyInstance [] ⟨[]⟩ [] .unit ⟨[]⟩ := by
  apply BodyInvokes.unit
      (inputTypes := [])
      (lexicalContext := unitBodyInstance.context)
      (finalContext := unitBodyInstance.context)
      (environment := []) (bound := ⟨[]⟩) (roots := [])
      (outcome := .fallthrough [])
  · exact unitEvidenceCovers
  · rfl
  · exact .nil
  · exact .nil _
  · exact .nil [] ⟨[]⟩
  · exact .nil
  · exact ⟨[], rfl⟩

/-- A nonempty semantic program can be admitted and run without consulting the
executable frontend or any backend evaluator. -/
theorem unitProgramEvaluates :
    ProgramEvaluates unitProgram unitEntry ⟨[]⟩ .unit ⟨[]⟩ := by
  exact .run unitProgramHasStages unitEntryValid unitBodyInvokes

/-- The public whole-program theorem closes a concrete nonempty semantic
program without accepting a preservation package as an extra premise. -/
theorem unitProgramEvaluationPreserved :
    ∃ bodyInstance,
      ProgramEntryValid unitProgram unitEntry ⟨[]⟩ bodyInstance ∧
        BodyInvocationPreserved bodyInstance ⟨[]⟩ ⟨[]⟩ .unit :=
  unitProgramEvaluates.preserves

end Solcore.Test.SourceSemanticsProgram
