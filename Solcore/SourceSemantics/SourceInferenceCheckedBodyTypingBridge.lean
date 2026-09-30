import Solcore.SourceSemantics.SourceProgramCheckingSoundness

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
    initial.InferenceReady →
    expectedReturn.VariablesBelow initial.inference.next →
    initial.LocalBindersBelowNextLocal →
    initial.NodesBelowNextOccurrence →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
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
  have patternsSubset : body.state.integerPatterns ⊆
      finalState.integerPatterns := by
    rw [Detail.unify_integerPatterns unified]
    intro pattern member
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
      initialInvariant initialReady returnBelow initialBindersBelow initialBelow
      substitutionExtends
      (by simpa only [checkedEq] using sourceExtends)
      patternsSubset requirementsSubset activeSignaturesEq activeParametersEq
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
