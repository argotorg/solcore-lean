import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.Internal.Inference.LetCertificates
import Solcore.SourceSemantics.SourceStageAnalysisSoundness
import Solcore.SourceSemantics.Staging.Program

/-!
# From inference soundness to the program judgment

The whole-program theorems, with one premise left:
`SourceInferenceSoundness.InferStatementsFuelSoundness`, the recursive soundness of statement
inference. Main theorems:
`SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound`,
`programHasStages_ofCheckProgram_and_analysis`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceCheckedBodyTypingBridge
/-!
The final bridge from recursive statement-inference soundness to the
checker-facing body proposition.  The recursive premise is tied to an actual
successful `inferStatementsFuel` call.  All remaining work here is structural:
the final source carrier, return-type unification, exact roots, and the unique
lexical extension of the checked input binders.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A fixed monomorphic input-binder sequence determines its final lexical
context uniquely.  This lets a single recursive typing derivation supply the
same `BodyFacts` to every input extension admitted by the checker header. -/
theorem monoBindersExtend_final_unique
    {owner : Resolved.DeclarationId} {base first second : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (left : MonoBindersExtend owner base binders types first)
    (right : MonoBindersExtend owner base binders types second) :
    first = second := by
  induction left generalizing second with
  | nil context =>
      cases right
      rfl
  | @cons context middle first binder binders type types scheme head tail ih =>
      cases right with
      | cons _ otherHead otherTail =>
          cases head
          cases otherHead
          exact ih otherTail

/-- Statement-root encoding is injective on lists. -/
private theorem statementRoots_injective
    {first second : List StatementId}
    (equal : first.map NodeId.statement = second.map NodeId.statement) :
    first = second := by
  induction first generalizing second with
  | nil =>
      cases second <;> simp at equal ⊢
  | cons head rest induction =>
      cases second with
      | nil => simp at equal
      | cons other others =>
          simp only [List.map_cons, List.cons.injEq] at equal
          rcases equal with ⟨headEq, restEq⟩
          have : head = other := NodeId.statement.inj headEq
          subst other
          simp [induction restEq]

private theorem monoBindersExtend_solvedRequirements_eq
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.solvedRequirements = base.solvedRequirements := by
  induction extension with
  | nil => rfl
  | cons _ head _ induction =>
      exact induction.trans head.context_fields.2.2.2.2

private theorem monoBindersExtend_signatures_eq
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.signatures = base.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head _ induction =>
      exact induction.trans head.context_fields.1

private theorem monoBindersExtend_scope_fields
    {owner : Resolved.DeclarationId}
    {base final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types final) :
    final.typeParameters = base.typeParameters ∧
      final.currentDeclaration = base.currentDeclaration ∧
        final.residualTypeVariables = base.residualTypeVariables := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons _ head _ induction =>
      exact ⟨induction.1.trans head.context_fields.2.2.1,
        induction.2.1.trans head.context_fields.2.1,
        induction.2.2.trans head.residualTypeVariables_eq⟩

/-- Return-type unification changes neither the owner, inputs, nor occurrence
nodes of the source carrier. -/
private theorem unify_toTypedSource_eq
    {state unified : State} {left right : Ty} {roots : List NodeId}
    (success : Detail.unify state left right = .ok unified) :
    unified.toTypedSource roots = state.toTypedSource roots := by
  have headerEq := Detail.unify_state_header success
  have ownerEq : unified.owner = state.owner := by
    have projected := congrArg State.Header.owner headerEq
    simpa [State.header] using projected
  have inputsEq : unified.inputs = state.inputs := by
    have projected := congrArg State.Header.inputs headerEq
    simpa [State.header] using projected
  have nodesEq := (Detail.unify_occurrenceState_eq success).1
  simp [State.toTypedSource, ownerEq, inputsEq, nodesEq]

/-- The scoped recursive theorem needed at the final checker boundary.
Unlike a hypothesis about arbitrary inferred children, it requires the
concrete successful call, its actual finalization resources, and coverage of
each returned statement root.  The latter is necessary for requirement
evidence in nested match/operator branches. -/
def InferStatementsFuelSoundness (fuel : Nat) : Prop :=
  ∀ {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementsFuel fuel inferenceContext statements expectedReturn
      initial = .ok result →
    FinalInferenceResources inferenceContext expectedReturn evidenceState roots
      finalized →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    ActiveLocalContextInvariant initial finalized.substitution semanticContext →
    ActiveSchemeQuantifierIsolation initial →
    initial.InferenceReady →
    expectedReturn.VariablesBelow initial.inference.next →
    initial.LocalBindersBelowNextLocal →
    initial.NodesBelowNextOccurrence →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    semanticContext.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures →
    semanticContext.typeParameters = inferenceContext.typeParameters →
    semanticContext.currentDeclaration =
      some inferenceContext.scope.genericOwner →
    semanticContext.residualTypeVariables = true →
    semanticContext.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements →
    (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
      semanticContext.assumptions →
    (∀ statement ∈ result.statements,
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement statement)) →
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementsHaveType finalized.typedSource
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution finalized.substitution result
        facts

/-- Once recursive statement inference has its closed soundness theorem, a
successful body check satisfies the statement-only checker proposition with
one shared facts witness for every compatible lexical context. -/
theorem checkedBodyStatementsHaveType_of_inferStatementsFuel_sound
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (header : CheckedBodyHeaderWellFormed signatures signature checked)
    (predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution) =
          signature.scheme.predicates)
    (signatureFormation : ProgramSignatureFormationValidated signatures)
    (functionsCanonical : ∀ candidate ∈ signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed signatures)
    (signatureParameters : SignatureParametersWellFormed signature.id
      signature.scheme.parameters)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked)
    (recursiveSound : InferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType signatures signature checked := by
  intro statements roots
  obtain ⟨declaration, body, finalState, result, found, inferred, unified,
    finalized, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  have declarationIdEq : declaration.id = signature.id :=
    (ProgramEnvironment.declaration?_sound found).2
  have substitutionEq : checked.substitution = result.substitution := by
    simp [checkedEq]
  obtain ⟨canonicalContext, canonicalExtension⟩ := header.inputs_extend
  let initial := State.initial declaration.id
    ((signature.parameterNames.zip signature.parameterTypes).map
      fun parameter => (parameter.1, Scheme.mono parameter.2))
    signature.parameterComptime
  have inputExtension : MonoBindersExtend declaration.id
      (checkedBodyContext signatures signature checked)
      (initial.localBinders.map
        (TypedBinder.applySubstitution result.substitution))
      signature.parameterTypes canonicalContext := by
    have inputsEq :=
      checkFunctionBody_success_typedBody_inputs success
    rw [inputsEq] at canonicalExtension
    rw [substitutionEq] at canonicalExtension
    rw [← declarationIdEq] at canonicalExtension
    simpa only [initial, State.initial_inputs_eq_localBinders] using
      canonicalExtension
  have initialInvariant : ActiveLocalContextInvariant initial
      result.substitution canonicalContext := by
    constructor
    · apply LocalEnvironmentAligned.ofInitialMonoBindersExtend
        declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map
          fun parameter => (parameter.1, Scheme.mono parameter.2))
        signature.parameterComptime result.substitution
        (context := checkedBodyContext signatures signature checked)
        (final := canonicalContext) (types := signature.parameterTypes)
        rfl rfl
      exact inputExtension
    · apply ActiveLocalFormation.ofMonoBindersExtend
      exact inputExtension
  have initialSchemeIsolation : ActiveSchemeQuantifierIsolation initial := by
    apply activeSchemeQuantifierIsolation_initial_mono
    intro entry member
    rcases List.mem_map.mp member with ⟨parameter, _, rfl⟩
    rfl
  have initialReady : initial.InferenceReady := by
    simpa only [initial] using State.InferenceReady.initial declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have returnBelow : (Ty.productMany signature.returnTypes).VariablesBelow
      initial.inference.next := by
    apply Ty.variablesBelow_productMany
    intro returnType member
    have closed := StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
      (header.return_types returnType member)
    intro metavariable free
    rw [closed] at free
    simp at free
  have initialBindersBelow : initial.LocalBindersBelowNextLocal := by
    simpa only [initial] using State.initial_localBindersBelowNextLocal
      declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have initialBelow : initial.NodesBelowNextOccurrence :=
    State.initial_nodesBelowNextOccurrence declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    initialReady signatureFormation functionsCanonical returnBelow inferred
  have returnBelowBody :
      (Ty.productMany signature.returnTypes).VariablesBelow
        body.state.inference.next :=
    returnBelow.weaken bodyProperties.1.next_le
  have unifyProgress : body.state.InferenceProgress finalState :=
    Detail.unify_inferenceProgress bodyProperties.2.1.solved
      bodyProperties.2.2 returnBelowBody unified
  have unifiedReady : finalState.InferenceReady :=
    Detail.unify_preserves_inferenceReady bodyProperties.2.1
      bodyProperties.2.2 returnBelowBody unified
  have sourceEq :
      (body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
        result.substitution = result.typedSource := by
    calc
      (body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
          result.substitution =
          (finalState.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
            result.substitution := by
              rw [unify_toTypedSource_eq unified]
      _ = result.typedSource := (Detail.finalize_typedSource finalized).symm
  have sourceExtends : TypingSourceExtends
      ((body.state.toTypedSource (body.statements.map NodeId.statement)).applySubstitution
        result.substitution) checked.typedBody := by
    rw [sourceEq, checkedEq]
    exact TypingSourceExtends.refl result.typedSource
  have rawSourceExtends : TypingSourceExtends
      (body.state.toTypedSource
        (body.statements.map NodeId.statement))
      (finalState.toTypedSource
        (body.statements.map NodeId.statement)) := by
    rw [unify_toTypedSource_eq unified]
    exact TypingSourceExtends.refl _
  have patternsSubset : body.state.integerPatterns ⊆
      finalState.integerPatterns := by
    rw [Detail.unify_integerPatterns unified]
    intro pattern member
    exact member
  have literalsSubset : body.state.integerLiterals ⊆
      finalState.integerLiterals := by
    rw [Detail.unify_integerLiterals unified]
    intro literal member
    exact member
  have requirementsSubset : body.state.requirements ⊆
      finalState.requirements := by
    rw [Detail.unify_requirements_eq unified]
    intro requirement member
    exact member
  let finalResources : FinalInferenceResources
      {
        environment
        signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates
      }
      (Ty.productMany signature.returnTypes) finalState
      (body.statements.map NodeId.statement) result :=
    FinalInferenceResources.ofFinalize finalized
  have substitutionExtends : result.substitution.SemanticallyExtends
      body.state.inference.substitution := by
    rw [finalResources.substitution_eq]
    exact (unifyProgress.trans
      (finalResources.progress_of_ready unifiedReady)).substitution_extends
  have activeSignaturesEq : canonicalContext.signatures =
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).signatures := by
    calc
      canonicalContext.signatures =
          (checkedBodyContext signatures signature checked).signatures :=
        monoBindersExtend_signatures_eq canonicalExtension
      _ = _ := by
        simp [checkedBodyContext, finalizedRequirementContext,
          declarationContext, Context.withResidualTypeVariables,
          Context.withSolvedRequirements, Context.withAssumptions,
          Context.forDeclaration]
  have scopeFields := monoBindersExtend_scope_fields canonicalExtension
  have activeParametersEq : canonicalContext.typeParameters =
      signature.scheme.parameters := by
    calc
      canonicalContext.typeParameters =
          (checkedBodyContext signatures signature checked).typeParameters :=
        scopeFields.1
      _ = signature.scheme.parameters := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables, Context.withSolvedRequirements,
          Context.withAssumptions, Context.forDeclaration]
  have activeDeclarationEq : canonicalContext.currentDeclaration =
      some declaration.id := by
    calc
      canonicalContext.currentDeclaration =
          (checkedBodyContext signatures signature checked
            ).currentDeclaration := scopeFields.2.1
      _ = some declaration.id := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables, Context.withSolvedRequirements,
          Context.withAssumptions, Context.forDeclaration,
          declarationIdEq]
  have activeResidual : canonicalContext.residualTypeVariables = true := by
    calc
      canonicalContext.residualTypeVariables =
          (checkedBodyContext signatures signature checked
            ).residualTypeVariables := scopeFields.2.2
      _ = true := by
        simp [checkedBodyContext, declarationContext,
          Context.withResidualTypeVariables]
  have activeRequirementsEq : canonicalContext.solvedRequirements =
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).solvedRequirements := by
    calc
      canonicalContext.solvedRequirements =
          (checkedBodyContext signatures signature checked
            ).solvedRequirements :=
        monoBindersExtend_solvedRequirements_eq canonicalExtension
      _ = _ := by
        simp [checkedBodyContext, finalizedRequirementContext,
          declarationContext, checkedEq, Context.withResidualTypeVariables,
          Context.withSolvedRequirements, Context.withAssumptions,
          Context.forDeclaration]
  have assumptionsMono :
      (finalizedRequirementContext
        {
          environment
          signatures
          scope := .ofDeclaration declaration
          typeParameters := signature.scheme.parameters
          assumptions := signature.scheme.predicates
        } result).assumptions ⊆ canonicalContext.assumptions := by
    have canonicalAssumptions :=
      MonoBindersExtend.assumptions_eq canonicalExtension
    have predicatesFixedResult :
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution result.substitution) =
            signature.scheme.predicates := by
      simpa only [checkedEq] using predicatesFixed
    intro predicate member
    rw [canonicalAssumptions]
    have substitutedMember : predicate ∈
        signature.scheme.predicates.map
          (TypedTraitResolution.applySubstitution result.substitution) := by
      simpa [finalizedRequirementContext, Context.withSolvedRequirements,
        Context.withAssumptions] using member
    rw [predicatesFixedResult] at substitutedMember
    simpa [checkedBodyContext, declarationContext,
      Context.withResidualTypeVariables, Context.withSolvedRequirements,
      Context.withAssumptions, Context.forDeclaration] using
      substitutedMember
  have rootCoverage : ∀ statement ∈ body.statements,
      TemplateScopeCovered result.typedSource canonicalContext
        (.statement statement) := by
    intro statement member
    apply TemplateScopeCovered.root finalResources.graph_closed.rootsHaveNoParent
    rw [finalize_statementRoots finalized]
    exact List.mem_map_of_mem member
  obtain ⟨finalContext, facts, _, typed, matching⟩ :=
    recursiveSound inferred finalResources signatureFormation functionsCanonical
      catalog (by simpa [ProgramTypeScope.ofDeclaration, declarationIdEq]
        using signatureParameters)
      initialInvariant initialSchemeIsolation initialReady returnBelow
      initialBindersBelow initialBelow
      substitutionExtends
      rawSourceExtends
      (by simpa only [checkedEq] using sourceExtends)
      patternsSubset literalsSubset requirementsSubset activeSignaturesEq
      activeParametersEq
      (by simpa [ProgramTypeScope.ofDeclaration] using activeDeclarationEq)
      activeResidual
      activeRequirementsEq assumptionsMono rootCoverage
  have expectedFixed : result.substitution.apply
      (Ty.productMany signature.returnTypes) =
        Ty.productMany signature.returnTypes := by
    have resultType : result.type = Ty.productMany signature.returnTypes := by
      simpa [checkedEq] using header.result_type
    exact (Detail.finalize_type finalized).symm.trans resultType
  have factsType : facts.type = Ty.productMany signature.returnTypes := by
    calc
      facts.type = result.substitution.apply body.type := matching.type_eq
      _ = result.substitution.apply
          (Ty.productMany signature.returnTypes) :=
        Detail.unify_then_finalize_eq unified finalized
      _ = Ty.productMany signature.returnTypes := expectedFixed
  have actualRoots : checked.typedBody.roots =
      body.statements.map NodeId.statement := by
    rw [checkedEq]
    exact finalize_statementRoots finalized
  have statementsEq : statements = body.statements := by
    have mapped : statements.map NodeId.statement =
        body.statements.map NodeId.statement := roots.symm.trans actualRoots
    exact statementRoots_injective mapped
  refine ⟨facts, factsType, ?_⟩
  intro lexicalContext extension
  have contextEq : lexicalContext = canonicalContext :=
    monoBindersExtend_final_unique extension canonicalExtension
  subst lexicalContext
  refine ⟨finalContext, ?_⟩
  subst statements
  have typedChecked : StatementsHaveType checked.typedBody
      { returnType := Ty.productMany signature.returnTypes }
      canonicalContext body.statements finalContext facts := by
    simpa only [checkedEq, expectedFixed] using typed
  exact typedChecked

/-- For an ordinary function, all global and rigid-parameter premises of the
recursive bridge come from the successful raw-workspace checker.  The body
header, closed predicates, and recursive theorem remain the separate semantic
inputs to this final assembly step. -/
theorem checkedBodyStatementsHaveType_ofCheckProgram_function
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {program : CheckedProgram}
    {signature : ProgramFunctionSignature} {function : CheckedFunction}
    (programSuccess : Frontend.checkProgram raw fuel = .ok program)
    (member : signature ∈ program.signatures.functions)
    (header : CheckedBodyHeaderWellFormed program.signatures signature
      function)
    (predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution function.substitution) =
          signature.scheme.predicates)
    (bodySuccess : checkFunctionBody program.environment program.signatures
      signature fuel = .ok function)
    (recursiveSound : InferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType program.signatures signature function := by
  apply checkedBodyStatementsHaveType_of_inferStatementsFuel_sound header
    predicatesFixed
  · exact Frontend.checkProgram_success_signature_formation programSuccess
  · intro candidate candidateMember
    exact (Frontend.checkProgram_success_function_signature_shape
      programSuccess candidateMember).2
  · exact SignatureCatalogWellFormed.ofCheckProgram programSuccess
  · exact (Frontend.checkProgram_success_signature_parameters_wellFormed
      programSuccess).functions signature member
  · exact bodySuccess
  · exact recursiveSound

/-- The synthetic function signature used for an implementation method has
the implementation's canonical rigid parameter row.  Its other global
premises are the same raw-checker facts as for ordinary functions. -/
theorem checkedBodyStatementsHaveType_ofCheckProgram_method
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {program : CheckedProgram}
    {implementation : ProgramImplementationSignature}
    {trait : ProgramTraitSignature}
    {method : ProgramImplMethodSignature} {function : CheckedFunction}
    (programSuccess : Frontend.checkProgram raw fuel = .ok program)
    (implementationMember :
      implementation ∈ program.signatures.implementations)
    (header : CheckedBodyHeaderWellFormed program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method)
      function)
    (predicatesFixed :
      (implementation.functionSignatureOfMethodWithTrait trait method
        ).scheme.predicates.map
        (TypedTraitResolution.applySubstitution function.substitution) =
      (implementation.functionSignatureOfMethodWithTrait trait method
        ).scheme.predicates)
    (bodySuccess : checkFunctionBody program.environment program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
        .ok function)
    (recursiveSound : InferStatementsFuelSoundness fuel) :
    CheckedBodyStatementsHaveType program.signatures
      (implementation.functionSignatureOfMethodWithTrait trait method)
      function := by
  apply checkedBodyStatementsHaveType_of_inferStatementsFuel_sound header
    predicatesFixed
  · exact Frontend.checkProgram_success_signature_formation programSuccess
  · intro candidate candidateMember
    exact (Frontend.checkProgram_success_function_signature_shape
      programSuccess candidateMember).2
  · exact SignatureCatalogWellFormed.ofCheckProgram programSuccess
  · simpa [ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using
      (Frontend.checkProgram_success_signature_parameters_wellFormed
        programSuccess).implementations implementation implementationMember
  · exact bodySuccess
  · exact recursiveSound

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceProgramBridge
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
jointly establish the independent whole-program staging judgment for the
checked program. No staging conclusion follows from static checking alone. -/
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
end
