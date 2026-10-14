import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

/-! Statement sequencing carries a source occurrence predicate alongside
whole-body evidence coverage. Actual generalized-initializer ancestry can
therefore follow each returned root without an unrelated child premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualStatementsFuel_with_selected_rooted_sources
    (invariant : Frontend.SourceInference.State →
      SourceSemantics.Context → Prop)
    (extra : Frontend.SourceInference.State → Prop)
    (rootScope : NodeId → Prop)
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    {evidenceState : Frontend.SourceInference.State}
    {ambientSource coverageSource : TypedSource}
    {control : ControlContext}
    {substitution : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (roots : List NodeId := [])
    (initialInvariant : invariant state semanticContext)
    (initialBelow : state.NodesBelowNextOccurrence)
    (resultExtension : ∀ id ∈ result.statements,
      SubtreePreserved substitution (result.state.toTypedSource roots)
        ambientSource (.statement id))
    (rawPreserved : ∀ id ∈ result.statements,
      RawSubtreePreserved (result.state.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.statement id))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (extraResult : extra result.state)
    (extraHead : ∀ {headFuel childFuel : Nat}
        {headInitial : Frontend.SourceInference.State}
        {headContext : SourceSemantics.Context}
        {headStatement : Syntax.Statement}
        {head : Detail.StatementResult} {tail : Detail.BlockResult}
        {remaining : List Syntax.Statement},
      invariant headInitial headContext →
      Detail.inferStatementFuel headFuel inferenceContext headStatement
        expectedReturn headInitial = .ok head →
      Detail.inferStatementsFuel childFuel inferenceContext remaining
        expectedReturn head.state = .ok tail →
      extra tail.state → extra head.state)
    (coveredStatements : ∀ id, id ∈ result.statements →
      TemplateScopeCovered coverageSource semanticContext (.statement id) ∧ rootScope (.statement id))
    (statementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {statement : Syntax.Statement} {head : Detail.StatementResult},
        childFuel < fuel →
        invariant input inputContext →
        Detail.inferStatementFuel childFuel inferenceContext statement
          expectedReturn input = .ok head →
        SubtreePreserved substitution (head.state.toTypedSource roots)
          ambientSource (.statement head.id) →
        RawSubtreePreserved (head.state.toTypedSource roots)
          (evidenceState.toTypedSource roots) (.statement head.id) →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        extra head.state →
        TemplateScopeCovered coverageSource inputContext (.statement head.id) ∧ rootScope (.statement head.id) →
        ∃ outputContext facts,
          invariant head.state outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution substitution)
            control inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution substitution head facts)
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn state = .ok result) :
    ∃ finalContext facts,
      invariant result.state finalContext ∧
      StatementsHaveType ambientSource control semanticContext
        result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution substitution result facts := by
  induction fuel generalizing statements state semanticContext result with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          have resultEq := inferStatementsFuel_success_nil_facts success
          subst result
          exact ⟨semanticContext, .empty, initialInvariant,
            .nil control semanticContext,
            BlockResultMatchesFactsAfterSubstitution.empty substitution state⟩
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              subst result
              have headCovered : TemplateScopeCovered coverageSource
                  semanticContext (.statement head.id) ∧ rootScope (.statement head.id) :=
                coveredStatements head.id (by simp)
              obtain ⟨finalContext, headFacts, finalInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess (resultExtension head.id (by simp))
                  (rawPreserved head.id (by simp)) integerPatternsSubset
                  requirementsSubset extraResult headCovered
              have headTypingAmbient :=
                (resultExtension head.id (by simp)).subgraph.statement headTyping (.inl rfl)
              exact ⟨finalContext, .singleton headFacts, finalInvariant,
                .singleton headTypingAmbient,
                BlockResultMatchesFactsAfterSubstitution.singleton headMatches⟩
          | cons next rest =>
              obtain ⟨head, tail, headSuccess, tailSuccess, resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              subst result
              have headBelow : head.state.NodesBelowNextOccurrence :=
                (Detail.inferStatementFuel_occurrenceBoundExtends headSuccess
                  ).nodesBelowNextOccurrence initialBelow
              have headToTail : TypingSourceExtends
                  (head.state.toTypedSource roots) (tail.state.toTypedSource roots) :=
                inferStatementsFuel_success_typingSourceExtends tailSuccess headBelow roots
              have headExtension : SubtreePreserved substitution
                  (head.state.toTypedSource roots) ambientSource (.statement head.id) :=
                (resultExtension head.id (by simp)).monoBefore headToTail
              have headRawPreserved : RawSubtreePreserved
                  (head.state.toTypedSource roots) (evidenceState.toTypedSource roots)
                  (.statement head.id) :=
                (rawPreserved head.id (by simp)).monoBefore headToTail
              have headIntegerPatternsSubset :
                  head.state.integerPatterns ⊆
                    evidenceState.integerPatterns :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_integerPatterns_subset
                    tailSuccess)
                  integerPatternsSubset
              have headRequirementsSubset :
                  head.state.requirements ⊆ evidenceState.requirements :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_requirements_subset tailSuccess)
                  requirementsSubset
              have headExtra : extra head.state :=
                extraHead initialInvariant headSuccess tailSuccess extraResult
              have headCovered : TemplateScopeCovered coverageSource
                  semanticContext (.statement head.id) ∧ rootScope (.statement head.id) :=
                coveredStatements head.id (by simp)
              obtain ⟨middleContext, headFacts, middleInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess headExtension headRawPreserved headIntegerPatternsSubset
                  headRequirementsSubset headExtra headCovered
              have headTypingAmbient :=
                headExtension.subgraph.statement headTyping (.inl rfl)
              have middleAssumptionsEq :
                  middleContext.assumptions = semanticContext.assumptions :=
                statementHasType_assumptions_eq headTypingAmbient
              have tailCovered : ∀ id, id ∈ tail.statements →
                  TemplateScopeCovered coverageSource middleContext
                    (.statement id) ∧ rootScope (.statement id) := by
                intro id member
                refine ⟨?_, (coveredStatements id (by simp [member])).2⟩
                intro owner scopes
                change owner.requirement.predicate ∈ middleContext.assumptions
                rw [middleAssumptionsEq]
                exact (coveredStatements id (by simp [member])).1 owner scopes
              obtain ⟨finalContext, tailFacts, finalInvariant, tailTyping,
                  tailMatches⟩ :=
                induction (statements := next :: rest)
                  (state := head.state) (result := tail)
                  (semanticContext := middleContext)
                  middleInvariant headBelow
                  (fun id member => resultExtension id (by simp [member]))
                  (fun id member => rawPreserved id (by simp [member]))
                  integerPatternsSubset requirementsSubset extraResult
                  tailCovered
                  (fun childBound childInvariant childSuccess childExtension childRawPreserved
                    childIntegerPatternsSubset childRequirementsSubset
                    childExtra childCovered =>
                    statementSound (Nat.lt_trans childBound
                      (Nat.lt_succ_self fuel)) childInvariant childSuccess
                      childExtension childRawPreserved childIntegerPatternsSubset
                      childRequirementsSubset childExtra childCovered)
                  tailSuccess
              obtain ⟨tailHead, tailRest, tailStatementsEq⟩ :=
                inferStatementsFuel_success_statements_eq_cons tailSuccess
              have sequenceTyping : StatementsHaveType ambientSource control
                  semanticContext (head.id :: tail.statements) finalContext
                  (.cons headFacts tailFacts) := by
                rw [tailStatementsEq]
                exact .cons headTypingAmbient
                  (by simpa [tailStatementsEq] using tailTyping)
              exact ⟨finalContext, .cons headFacts tailFacts, finalInvariant,
                sequenceTyping,
                BlockResultMatchesFactsAfterSubstitution.cons headMatches
                  tailMatches⟩

/-- Sequential statements preserve the type scope of the expected return. -/
theorem selected_statement_return_admissible
    {source : TypedSource} {control : ControlContext}
    {before after : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {type : Ty}
    (typing : StatementHasType source control before id after facts)
    (admissible : TypeAdmissible before type) :
    TypeAdmissible after type := by
  have fields := statementHasType_nonlocal_fields_eq typing
  have variables : after.typeVariables = before.typeVariables := by
    cases typing <;> try rfl
    all_goals
      exact BinderExtends.typeVariables_eq
        (by assumption : BinderExtends source.owner before _ after)
  exact StructuralSubstitution.TypeAdmissible.transportContext
    fields.1 fields.2.1 fields.2.2.1 variables fields.2.2.2.1 admissible

theorem actualInferStatementsFuelRootedSoundness_of_selected_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      ActualInferStatementFuelRootedSoundness childFuel) :
    ActualInferStatementsFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    initialInvariant actual operational returnAdmissible finalSubstitutionExtension resultExtension
    rawResultExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    actualStatementsFuel_with_selected_rooted_sources
      (fun state context => RecursiveStatementInvariant wholeContext
        expectedReturn finalized state context ∧ ActualContext wholeContext finalized frames context ∧
        ActualStateInvariant state (evidenceState.toTypedSource roots) ∧
        TypeAdmissible context (finalized.substitution.apply expectedReturn))
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals)
      (ActualContext.Covers finalized frames)
      (roots := roots) ⟨initialInvariant, actual, operational, returnAdmissible⟩ initialInvariant.nodesBelow
      resultExtension rawResultExtension integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset⟩
      (by
        intro headFuel childFuel headInitial headContext headStatement head
          tail remaining headInvariant headSuccess tailSuccess tailExtra
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.1.ready signatureFormation functionsCanonical
          headInvariant.1.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.1.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2⟩)
      (fun id member => ⟨covered id member, actualCovered id member⟩)
      (by
        intro childFuel input inputContext statement head childBound childInvariant childSuccess childExtension childRawPreserved
          childIntegerPatternsSubset childRequirementsSubset childExtra childCovered
        obtain ⟨context, facts, invariant, actual, operational, typed, agreement⟩ :=
          statementSound _ childBound childSuccess resources interfaces signaturesEq
            ownerEq parametersEq assumptionsEq signatureFormation
            functionsCanonical catalog signatureParameters childInvariant.1 childInvariant.2.1 childInvariant.2.2.1 childInvariant.2.2.2
            childExtra.1 childExtension childRawPreserved
            childIntegerPatternsSubset childExtra.2
            childRequirementsSubset childCovered.1 childCovered.2
        have admissible := selected_statement_return_admissible typed childInvariant.2.2.2
        exact ⟨context, facts, ⟨invariant, actual, operational, admissible⟩, typed, agreement⟩)
      success
  exact ⟨finalContext, facts, finalInvariant.1, finalInvariant.2.1, finalInvariant.2.2.1, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
