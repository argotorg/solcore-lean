import Solcore.SourceSemantics.Program

/-! The stored statement annotations determine the legacy type/value/return
summary across independent declarative contexts and controls. Occurrence
uniqueness identifies the physical statement node; the mutual typing proof
compares the exact branch bodies and ordered match rows. No expected-result
or control-frame equality is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness

open Frontend SourceInference

private def statementFlags (facts : StatementFacts) : Bool × Bool :=
  (facts.hasValue, facts.sawReturn)

private def bodySummary (facts : BodyFacts) : TypeSystem.Ty × Bool :=
  (facts.type, facts.sawReturn)

private theorem node_annotation
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType source control context id final facts) :
    ∃ node, ContainsStatement source id node ∧ facts.type = node.type := by
  cases typing
  all_goals refine ⟨_, by assumption, ?_⟩
  all_goals symm; assumption

private theorem statement_type_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    leftFacts.type = rightFacts.type := by
  obtain ⟨leftNode, leftContains, leftAnnotation⟩ := node_annotation left
  obtain ⟨rightNode, rightContains, rightAnnotation⟩ := node_annotation right
  have same : leftNode = rightNode := Option.some.inj
    ((lookupStatement?_complete unique leftContains).symm.trans
      (lookupStatement?_complete unique rightContains))
  exact leftAnnotation.trans ((congrArg StatementNode.type same).trans rightAnnotation.symm)

private theorem all_returns_eq {left right : List BodyFacts}
    (same : left.map bodySummary = right.map bodySummary) :
    allBodiesSawReturn left = allBodiesSawReturn right := by
  have projected := congrArg (fun rows : List (TypeSystem.Ty × Bool) =>
    rows.all Prod.snd) same
  simpa only [List.all_map, Function.comp_def, bodySummary,
    allBodiesSawReturn] using projected

/-- Every nontrivial motive quantifies over a second independent derivation.
The expression, assignment and header judgments carry no summary obligation.
The local node and annotation lemmas are exact consequences of the two actual
membership/typing receipts, rather than new source assumptions. -/
local macro "summary_induction" "(" recursor:term "," source:term ","
    unique:term "," typing:term ")" : term =>
  `(by
    have nodeUnique : ∀ {id : StatementId} {left right : StatementNode},
        ContainsStatement $source id left → ContainsStatement $source id right →
        left = right := by
      intro id left right first second
      exact Option.some.inj
        ((lookupStatement?_complete $unique first).symm.trans
          (lookupStatement?_complete $unique second))
    have annotationUnique :
        ∀ {leftControl rightControl : ControlContext}
          {leftContext leftFinal rightContext rightFinal : Context}
          {id : StatementId} {leftFacts rightFacts : StatementFacts},
          StatementHasType $source leftControl leftContext id leftFinal leftFacts →
          StatementHasType $source rightControl rightContext id rightFinal rightFacts →
          leftFacts.type = rightFacts.type := by
      intro leftControl rightControl leftContext leftFinal rightContext rightFinal
        id leftFacts rightFacts left right
      exact statement_type_eq $unique left right
    intro otherControl otherContext otherFinal otherFacts
    refine $recursor (source := $source) (t := $typing)
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ _ => True)
      (motive_7 := fun _ _ _ => True)
      (motive_8 := fun _ _ id _ facts _ =>
        ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
          {otherFacts : StatementFacts}
          (other : StatementHasType $source otherControl otherContext id
            otherFinal otherFacts),
          statementFlags facts = statementFlags otherFacts)
      (motive_9 := fun _ _ statements _ facts _ =>
        ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
          {otherFacts : BodyFacts}
          (other : StatementsHaveType $source otherControl otherContext statements
            otherFinal otherFacts),
          bodySummary facts = bodySummary otherFacts)
      (motive_10 := fun _ _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ _ => True)
      (motive_12 := fun _ _ _ arm facts _ =>
        ∀ {otherControl : ControlContext} {otherContext : Context}
          {otherType : TypeSystem.Ty} {otherFacts : BodyFacts}
          (other : MatchCaseHasType $source otherControl otherContext otherType
            arm otherFacts),
          bodySummary facts = bodySummary otherFacts)
      (motive_13 := fun _ _ _ arms facts _ =>
        ∀ {otherControl : ControlContext} {otherContext : Context}
          {otherType : TypeSystem.Ty} {otherFacts : List BodyFacts}
          (other : MatchCasesHaveType $source otherControl otherContext otherType
            arms otherFacts),
          facts.map bodySummary = otherFacts.map bodySummary)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try { intros; exact True.intro }
    all_goals intros
    all_goals rename_i other
    all_goals cases other
    all_goals grind [statementFlags, bodySummary, BodyFacts.empty,
      BodyFacts.singleton, BodyFacts.cons, all_returns_eq])

private theorem statement_flags_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    statementFlags leftFacts = statementFlags rightFacts := by
  have result :
      ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
        {otherFacts : StatementFacts},
        StatementHasType source otherControl otherContext id otherFinal otherFacts →
        statementFlags leftFacts = statementFlags otherFacts :=
    summary_induction(StatementHasType.rec, source, unique, left)
  exact result right

/-- The same physical statement fixes its type, value flag and return flag,
without identifying the two lexical contexts or control contexts. -/
theorem statement_summary_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {id : StatementId} {leftFacts rightFacts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementHasType source leftControl leftContext id leftFinal leftFacts)
    (right : StatementHasType source rightControl rightContext id rightFinal rightFacts) :
    leftFacts.type = rightFacts.type ∧
      leftFacts.hasValue = rightFacts.hasValue ∧
      leftFacts.sawReturn = rightFacts.sawReturn := by
  have flags := statement_flags_eq unique left right
  exact ⟨statement_type_eq unique left right,
    congrArg Prod.fst flags, congrArg Prod.snd flags⟩

/-- Ordered statement lists have the same annotated type and return flag under
any two actual declarative typing derivations at the same unique source. -/
theorem statements_summary_eq
    {source : TypedSource} {leftControl rightControl : ControlContext}
    {leftContext leftFinal rightContext rightFinal : Context}
    {statements : List StatementId} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : StatementsHaveType source leftControl leftContext statements leftFinal leftFacts)
    (right : StatementsHaveType source rightControl rightContext statements rightFinal rightFacts) :
    leftFacts.type = rightFacts.type ∧ leftFacts.sawReturn = rightFacts.sawReturn := by
  have result :
      ∀ {otherControl : ControlContext} {otherContext otherFinal : Context}
        {otherFacts : BodyFacts},
        StatementsHaveType source otherControl otherContext statements otherFinal otherFacts →
        bodySummary leftFacts = bodySummary otherFacts :=
    summary_induction(StatementsHaveType.rec, source, unique, left)
  have same := result right
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- BodyHasType alone retains its actual facts annotation; it does not equate
that annotation with the declaration's expected result. -/
theorem body_facts_type_eq
    {source : TypedSource} {leftContext rightContext : Context}
    {leftResult rightResult : TypeSystem.Ty} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : BodyHasType source leftContext leftResult leftFacts)
    (right : BodyHasType source rightContext rightResult rightFacts) :
    leftFacts.type = rightFacts.type := by
  obtain ⟨leftFinal, leftTyped, _, _⟩ := left
  obtain ⟨rightFinal, rightTyped, _, _⟩ := right
  exact (statements_summary_eq unique leftTyped rightTyped).1

/-- Independent annotation equations identify the declaration results once
the actual body facts have been compared. These equations are fields of the
original BodyDefinitionHasType judgment, not desired-result assumptions. -/
theorem annotated_result_eq
    {source : TypedSource} {leftContext rightContext : Context}
    {leftResult rightResult : TypeSystem.Ty} {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique source)
    (left : BodyHasType source leftContext leftResult leftFacts)
    (right : BodyHasType source rightContext rightResult rightFacts)
    (leftAnnotation : leftFacts.type = leftResult)
    (rightAnnotation : rightFacts.type = rightResult) :
    leftResult = rightResult :=
  leftAnnotation.symm.trans ((body_facts_type_eq unique left right).trans rightAnnotation)

private theorem definition_annotation
    {signatures : ProgramSignatures} {parameters : List TypeSystem.TypeParameterId}
    {assumptions : List ProgramPredicate} {parameterNames : List String}
    {parameterTypes returnTypes : List TypeSystem.Ty}
    {parameterComptime : List Bool} {returnComptime : Bool}
    {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions parameterNames
      parameterTypes parameterComptime returnTypes returnComptime definition facts) :
    ∃ context, BodyHasType definition.source context definition.resultType facts ∧
      facts.type = definition.resultType := by
  cases typing with
  | @intro lexicalContext _ _ _ _ _ resultType _ _ _ _ _ _ _ _ bodyTyped annotation =>
      refine ⟨lexicalContext, ?_, annotation.trans resultType.symm⟩
      simpa only [resultType] using bodyTyped

/-- Two genuine declaration-body judgments with the same source have the
same declared result, even when their signatures, parameter contexts and
control return indices differ. Both result annotations are extracted from
those original judgments. -/
theorem definition_result_eq
    {leftSignatures rightSignatures : ProgramSignatures}
    {leftParameters rightParameters : List TypeSystem.TypeParameterId}
    {leftAssumptions rightAssumptions : List ProgramPredicate}
    {leftNames rightNames : List String}
    {leftParameterTypes rightParameterTypes leftReturnTypes rightReturnTypes :
      List TypeSystem.Ty}
    {leftParameterComptime rightParameterComptime : List Bool}
    {leftReturnComptime rightReturnComptime : Bool}
    {leftDefinition rightDefinition : BodyDefinition}
    {leftFacts rightFacts : BodyFacts}
    (unique : NodeOccurrencesUnique leftDefinition.source)
    (sameSource : leftDefinition.source = rightDefinition.source)
    (left : BodyDefinitionHasType leftSignatures leftParameters leftAssumptions
      leftNames leftParameterTypes leftParameterComptime leftReturnTypes
      leftReturnComptime leftDefinition leftFacts)
    (right : BodyDefinitionHasType rightSignatures rightParameters rightAssumptions
      rightNames rightParameterTypes rightParameterComptime rightReturnTypes
      rightReturnComptime rightDefinition rightFacts) :
    leftDefinition.resultType = rightDefinition.resultType := by
  obtain ⟨leftContext, leftTyped, leftAnnotation⟩ := definition_annotation left
  obtain ⟨rightContext, rightTyped, rightAnnotation⟩ := definition_annotation right
  have rightAtLeft : BodyHasType leftDefinition.source rightContext
      rightDefinition.resultType rightFacts := by
    rw [sameSource]
    exact rightTyped
  exact annotated_result_eq unique leftTyped rightAtLeft leftAnnotation rightAnnotation

end Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness
