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

/-- The exact recursive theorem needed at the final checker boundary.  Unlike
a hypothesis about arbitrary inferred children, it requires the concrete
successful call and the standard initial, source, and evidence invariants. -/
def InferStatementsFuelSoundness (fuel : Nat) : Prop :=
  ∀ {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement} {expectedReturn : Ty}
    {initial : State} {result : Detail.BlockResult}
    {outer : Substitution} {ambientSource : TypedSource}
    {evidenceState : State} {roots : List NodeId}
    {semanticContext : SourceSemantics.Context},
    Detail.inferStatementsFuel fuel inferenceContext statements expectedReturn
      initial = .ok result →
    ActiveLocalContextInvariant initial outer semanticContext →
    initial.NodesBelowNextOccurrence →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      ambientSource →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.requirements ⊆ evidenceState.requirements →
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementsHaveType ambientSource
        { returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution outer result facts

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
  have initialBelow : initial.NodesBelowNextOccurrence :=
    State.initial_nodesBelowNextOccurrence declaration.id
      ((signature.parameterNames.zip signature.parameterTypes).map
        fun parameter => (parameter.1, Scheme.mono parameter.2))
      signature.parameterComptime
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
  obtain ⟨finalContext, facts, _, typed, matching⟩ :=
    recursiveSound inferred initialInvariant initialBelow sourceExtends
      patternsSubset requirementsSubset
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
    simpa only [expectedFixed] using typed
  exact typedChecked

end Solcore.SourceSemantics.SourceInferenceSoundness
