import Solcore.SourceSemantics.SourceInferenceExpressionCallSoundness

/-!
Top-level operational inversion for source call expressions.

The call implementation contains several pieces of name-resolution control
flow before reaching one of the four semantic tails.  This module records
only the successful tail which was actually executed.  In particular, the
selected-call case retains whether its candidate row came from qualified or
unqualified lookup, so catalog membership is recovered without a hypothetical
lookup premise.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- Every outgoing occurrence edge of one expression root survives in an
eventual evidence source.  This permits selected-call attachment to rewrite
the root's type and coercion metadata while retaining its expression form. -/
def ExpressionDirectChildrenRetainedAt
    (before after : TypedSource) (parent : ExpressionId) : Prop :=
  ∀ {child : NodeId},
    DirectChild before (.expression parent) child →
      DirectChild after (.expression parent) child

namespace ExpressionDirectChildrenRetainedAt

theorem trans
    {first second third : TypedSource} {parent : ExpressionId}
    (left : ExpressionDirectChildrenRetainedAt first second parent)
    (right : ExpressionDirectChildrenRetainedAt second third parent) :
    ExpressionDirectChildrenRetainedAt first third parent := by
  intro child edge
  exact right (left edge)

/-- Exact node-table equality preserves all outgoing expression edges. -/
theorem ofNodesEq
    {before after : TypedSource} {parent : ExpressionId}
    (nodesEq : after.nodes = before.nodes) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  rcases edge with ⟨node, contains, member⟩
  exact ⟨node, ⟨by rw [nodesEq]; exact contains.1, contains.2⟩, member⟩

/-- A raw append-only prefix may precede any eventual retained edge map. -/
theorem monoBefore
    {before middle after : TypedSource} {parent : ExpressionId}
    (extension : TypingSourceExtends before middle)
    (retained : ExpressionDirectChildrenRetainedAt middle after parent) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  rcases edge with ⟨node, contains, member⟩
  apply retained
  exact ⟨node,
    ⟨extension.nodes_prefix.subset contains.1, contains.2⟩, member⟩

/-- Exact preservation of a substituted expression node preserves all of its
form references, and hence every direct child edge. -/
theorem ofExpressionNodesPreservedAt
    {before after : TypedSource} {parent : ExpressionId}
    {substitution : TypeSystem.Substitution}
    (preserved : ExpressionNodesPreservedAt [parent]
      (before.applySubstitution substitution) after) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  intro child edge
  have substitutedEdge :=
    FlexibleSubstitution.directChild_applySubstitution substitution edge
  rcases substitutedEdge with ⟨node, contains, childMember⟩
  cases node with
  | statement statementNode =>
      have impossible : (NodeId.statement statementNode.id) =
          .expression parent := contains.2
      cases impossible
  | expression expressionNode =>
      have parentIdEq : expressionNode.id = parent := by
        have wrapped : NodeId.expression expressionNode.id =
            .expression parent := contains.2
        injection wrapped
      have expressionContains : ContainsExpression
          (before.applySubstitution substitution) parent expressionNode :=
        ⟨contains.1, parentIdEq⟩
      have finalContains : ContainsExpression after parent expressionNode :=
        preserved (by simp) expressionContains
      exact ⟨.expression expressionNode,
        ⟨finalContains.1, congrArg NodeId.expression finalContains.2⟩,
        childMember⟩

theorem ofTypingSourceExtends
    {before after : TypedSource} {parent : ExpressionId}
    (substitution : TypeSystem.Substitution)
    (extension : TypingSourceExtends
      (before.applySubstitution substitution) after) :
    ExpressionDirectChildrenRetainedAt before after parent := by
  exact ofExpressionNodesPreservedAt
    (ExpressionNodesPreservedAt.ofTypingSourceExtends extension)

/-- Delayed-coercion attachment preserves expression forms and their child
references even at roots whose type and requirement rows are rewritten. -/
theorem ofAttachExpressionCoercions
    (state : Frontend.SourceInference.State)
    (entries : List Detail.ExpressionCoercions)
    (roots : List NodeId) (parent : ExpressionId) :
    ExpressionDirectChildrenRetainedAt (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots)
      parent := by
  induction entries generalizing state with
  | nil =>
      intro child edge
      simpa [Detail.attachExpressionCoercions] using edge
  | cons entry entries induction =>
      let next := state.modifyExpressionNode entry.expression fun node =>
        Detail.appendExpressionCoercions node entry.coercions
      have step : ExpressionDirectChildrenRetainedAt
          (state.toTypedSource roots) (next.toTypedSource roots) parent := by
        intro child edge
        rcases edge with ⟨node, contains, childMember⟩
        cases node with
        | statement statementNode =>
            have impossible : (NodeId.statement statementNode.id) =
                .expression parent := contains.2
            cases impossible
        | expression expressionNode =>
            have parentIdEq : expressionNode.id = parent := by
              have wrapped : NodeId.expression expressionNode.id =
                  .expression parent := contains.2
              injection wrapped
            have expressionContains : ContainsExpression
                (state.toTypedSource roots) parent expressionNode :=
              ⟨contains.1, parentIdEq⟩
            by_cases targetEq : parent = entry.expression
            · have expressionTargetEq : expressionNode.id =
                  entry.expression := parentIdEq.trans targetEq
              have targetContains : ContainsExpression
                  (state.toTypedSource roots) entry.expression
                  expressionNode := ⟨contains.1, expressionTargetEq⟩
              have modifiedContains :=
                modifyExpressionNode_containsExpression_self state
                  entry.expression expressionNode
                  (fun node => Detail.appendExpressionCoercions node
                    entry.coercions)
                  roots targetContains
              let modifiedNode : ExpressionNode := {
                Detail.appendExpressionCoercions expressionNode
                    entry.coercions with
                id := entry.expression
              }
              refine ⟨.expression modifiedNode,
                ⟨modifiedContains.1, ?_⟩, ?_⟩
              · exact (congrArg NodeId.expression modifiedContains.2).trans
                  (congrArg NodeId.expression targetEq.symm)
              simpa [modifiedNode, Detail.appendExpressionCoercions,
                nodeChildIds, Node.references] using childMember
            · have modifiedContains :=
                modifyExpressionNode_containsExpression_other state
                  entry.expression parent expressionNode
                  (fun node => Detail.appendExpressionCoercions node
                    entry.coercions)
                  roots targetEq expressionContains
              exact ⟨.expression expressionNode,
                ⟨modifiedContains.1,
                  congrArg NodeId.expression modifiedContains.2⟩,
                childMember⟩
      change ExpressionDirectChildrenRetainedAt (state.toTypedSource roots)
        ((Detail.attachExpressionCoercions next entries).toTypedSource roots)
        parent
      exact step.trans (induction (state := next))

end ExpressionDirectChildrenRetainedAt

/-- Operational provenance for the candidate row of a selected direct call. -/
inductive SelectedCallCandidatesOrigin
    (context : Frontend.SourceInference.Context) :
    String → List ProgramFunctionSignature → Prop where
  | unqualified
      {name : String} {candidates : List ProgramFunctionSignature}
      (lookup : Detail.functionsNamed context name = .ok candidates) :
      SelectedCallCandidatesOrigin context name candidates
  | qualified
      {namespacePath : List String} {name : String}
      {candidates : List ProgramFunctionSignature}
      (lookup : Detail.qualifiedFunctionsNamed context namespacePath name =
        .ok (some candidates)) :
      SelectedCallCandidatesOrigin context
        (String.intercalate "." (namespacePath ++ [name])) candidates

theorem SelectedCallCandidatesOrigin.candidatesSubset
    {context : Frontend.SourceInference.Context}
    {name : String} {candidates : List ProgramFunctionSignature}
    (origin : SelectedCallCandidatesOrigin context name candidates) :
    candidates ⊆ context.signatures.functions := by
  cases origin with
  | unqualified lookup =>
      exact Detail.functionsNamed_success_subset_catalog lookup
  | qualified lookup =>
      exact Detail.qualifiedFunctionsNamed_success_subset_catalog lookup

/-- Recursive expression soundness at a node which may subsequently be
rewritten by delayed coercion attachment.  The ordinary bounded callback
uses an append-only ambient node source; selected-call arguments instead
carry occurrence-scoped requirement retention into the eventual evidence
source.  The operational provenance still ties every invocation to the
enclosing computation and its final ledgers. -/
def RetainedExpressionChildTypingCallback
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource semanticSource evidenceSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (context : SourceSemantics.Context)
    (substitution : TypeSystem.Substitution)
    (roots : List NodeId) : Prop :=
  ∀ child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      ambientNodeSource evidenceState roots,
    ExpressionRequirementsRetainedAt (child.final.toTypedSource roots)
        evidenceSource child.inferred.id →
      ExpressionTypingBase (child.final.toTypedSource roots) semanticSource
        context substitution child.inferred

/-- The recursive boundary needed by a closed whole-body theorem.  Besides
operational provenance and requirement retention, every invocation carries
both the final scope-coverage fact and preservation of every raw outgoing
edge of that actual child occurrence.  Coverage is not implied by source
extension; the enclosing expression form supplies it from its concrete
direct-child edge and the final closed occurrence graph.  Edge preservation
is the extra invariant needed across selected-call coercion attachment, which
may rewrite the child root without changing its form or references. -/
def CoveredRetainedExpressionChildTypingCallback
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource semanticSource evidenceSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (context : SourceSemantics.Context)
    (substitution : TypeSystem.Substitution)
    (roots : List NodeId) : Prop :=
  ∀ child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      ambientNodeSource evidenceState roots,
    child.initial.InferenceReady →
      (∀ expectedType ∈ child.expected,
        expectedType.VariablesBelow child.initial.inference.next) →
      ActiveLocalContextInvariant child.initial substitution context →
      child.initial.LocalBindersBelowNextLocal →
      ExpressionRequirementsRetainedAt (child.final.toTypedSource roots)
          evidenceSource child.inferred.id →
        ExpressionDirectChildrenRetainedAt (child.final.toTypedSource roots)
            evidenceSource child.inferred.id →
          TemplateScopeCovered evidenceSource context
              (.expression child.inferred.id) →
            ExpressionTypingBase (child.final.toTypedSource roots)
              semanticSource context substitution child.inferred

/-- Attachment retains the old requirements of every argument whenever the
attachment row is known to carry exactly the source-ordered argument ids.
Unlike `argumentRequirementsRetainedAt_attachExpressionCoercions`, this
operational adapter does not require semantic coercion validity first; that
validity is itself proved later from the recursive argument bases. -/
theorem argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
    {state : Frontend.SourceInference.State}
    {roots : List NodeId} {evidenceSource : TypedSource}
    {substitution : TypeSystem.Substitution}
    {arguments : List InferredExpression}
    {entries : List Detail.ExpressionCoercions}
    (expressionIds : entries.map (·.expression) = arguments.map (·.id))
    (argumentIdsUnique : (arguments.map (·.id)).Nodup)
    (preserved : ExpressionNodesPreservedAt (arguments.map (·.id))
      ((Detail.attachExpressionCoercions state entries
        |>.toTypedSource roots).applySubstitution substitution)
      evidenceSource) :
    ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt (state.toTypedSource roots)
        evidenceSource argument.id := by
  intro argument argumentMember
  have argumentIdMember : argument.id ∈ arguments.map (·.id) :=
    List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
  have entryIdMember : argument.id ∈ entries.map (·.expression) := by
    rw [expressionIds]
    exact argumentIdMember
  obtain ⟨entry, entryMember, entryIdEq⟩ := List.mem_map.mp entryIdMember
  have entriesUnique : (entries.map (·.expression)).Nodup := by
    rw [expressionIds]
    exact argumentIdsUnique
  have entryPreserved : ExpressionNodesPreservedAt [entry.expression]
      ((Detail.attachExpressionCoercions state entries
        |>.toTypedSource roots).applySubstitution substitution)
      evidenceSource := by
    intro id node idMember contains
    have idEq : id = entry.expression := by simpa using idMember
    subst id
    apply preserved
    · rw [entryIdEq]
      exact argumentIdMember
    · exact contains
  have retained : ExpressionRequirementsRetainedAt (state.toTypedSource roots)
      evidenceSource entry.expression :=
    ExpressionRequirementsRetainedAt.ofAttachExpressionCoercions
      entriesUnique entryMember entryPreserved
  rw [entryIdEq] at retained
  intro node requirement contains requirementMember
  exact retained contains requirementMember

/-- A source-ordered argument traversal produces pre-attachment bases when
each argument occurrence is known to retain its owned requirements in the
eventual evidence source.  This is the selected-call analogue of
`inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded`:
the child-to-argument-state source links remain append-only, while the final
argument roots themselves may be rewritten by coercion attachment. -/
theorem
    inferExprsFuel_success_argumentTypingBasesValid_under_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {semanticSource evidenceSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (integerPatternsSubset :
      final.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ∀ argument ∈ inferred,
      ExpressionRequirementsRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState target outer roots)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final)) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource target
      outer inferred := by
  induction fuel generalizing expressions initial inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext
              expression none initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext
                  rest headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferExprsFuel_success_typingSourceExtends_under_bound
                      tailSuccess headBelow roots
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerLiterals_subset tailSuccess)
                      integerLiteralsSubset
                  have headIntegerPatternsSubset :
                      headState.integerPatterns ⊆
                        evidenceState.integerPatterns :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerPatterns_subset tailSuccess)
                      integerPatternsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_requirements_subset tailSuccess)
                      requirementsSubset
                  let child : ExpressionChildInferenceProvenance parentFuel
                      inferenceContext (final.toTypedSource roots)
                      evidenceState roots := {
                    fuel
                    expression
                    expected := none
                    initial
                    final := headState
                    inferred := head
                    fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToFinal
                    integerPatternsSubset := headIntegerPatternsSubset
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headRetainedAtFinal : ExpressionRequirementsRetainedAt
                      (final.toTypedSource roots) evidenceSource head.id :=
                    retained head (by simp)
                  have headRetained : ExpressionRequirementsRetainedAt
                      (headState.toTypedSource roots) evidenceSource head.id :=
                    ExpressionRequirementsRetainedAt.monoBefore headToFinal
                      headRetainedAtFinal
                  have headBase := childSound child headRetained
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt)
                    (initialBelow := headBelow)
                    (integerPatternsSubset := integerPatternsSubset)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    (retained := by
                      intro argument member
                      exact retained argument (by simp [member]))
                    (childSound := childSound)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Coverage-aware form of the retained argument sequencer.  Membership in
the successful traversal supplies both the argument's eventual retention and
its scope coverage before the recursive callback is invoked. -/
theorem
    inferExprsFuel_success_argumentTypingBasesValid_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {semanticSource evidenceSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialReady : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial outer target)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (integerPatternsSubset :
      final.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ∀ argument ∈ inferred,
      ExpressionRequirementsRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (childrenRetained : ∀ argument ∈ inferred,
      ExpressionDirectChildrenRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (covered : ∀ argument ∈ inferred,
      TemplateScopeCovered evidenceSource target (.expression argument.id))
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState target outer roots)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final)) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource target
      outer inferred := by
  induction fuel generalizing expressions initial inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext
              expression none initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext
                  rest headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferExprsFuel_success_typingSourceExtends_under_bound
                      tailSuccess headBelow roots
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerLiterals_subset tailSuccess)
                      integerLiteralsSubset
                  have headIntegerPatternsSubset :
                      headState.integerPatterns ⊆
                        evidenceState.integerPatterns :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerPatterns_subset tailSuccess)
                      integerPatternsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_requirements_subset tailSuccess)
                      requirementsSubset
                  let child : ExpressionChildInferenceProvenance parentFuel
                      inferenceContext (final.toTypedSource roots)
                      evidenceState roots := {
                    fuel
                    expression
                    expected := none
                    initial
                    final := headState
                    inferred := head
                    fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToFinal
                    integerPatternsSubset := headIntegerPatternsSubset
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headRetainedAtFinal : ExpressionRequirementsRetainedAt
                      (final.toTypedSource roots) evidenceSource head.id :=
                    retained head (by simp)
                  have headRetained : ExpressionRequirementsRetainedAt
                      (headState.toTypedSource roots) evidenceSource head.id :=
                    ExpressionRequirementsRetainedAt.monoBefore headToFinal
                      headRetainedAtFinal
                  have headProperties := Detail.inferExprFuel_inferenceProperties
                    initialReady signatureFormation functionsCanonical (by
                      intro expectedType member
                      simp at member) headSuccess
                  have headInvariant : ActiveLocalContextInvariant headState
                      outer target :=
                    initialInvariant.inferExprFuel headSuccess
                  have headBindersBelow :
                      headState.LocalBindersBelowNextLocal :=
                    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
                      initialBindersBelow headSuccess
                  have headChildrenRetainedAtFinal :
                      ExpressionDirectChildrenRetainedAt
                        (final.toTypedSource roots) evidenceSource head.id :=
                    childrenRetained head (by simp)
                  have headChildrenRetained :
                      ExpressionDirectChildrenRetainedAt
                        (headState.toTypedSource roots) evidenceSource
                        head.id :=
                    ExpressionDirectChildrenRetainedAt.monoBefore headToFinal
                      headChildrenRetainedAtFinal
                  have headCovered : TemplateScopeCovered evidenceSource
                      target (.expression head.id) :=
                    covered head (by simp)
                  have headBase := childSound child initialReady (by
                      intro expectedType member
                      simp at member)
                    initialInvariant initialBindersBelow headRetained
                    headChildrenRetained headCovered
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt)
                    (initialReady := headProperties.2.1)
                    (initialBelow := headBelow)
                    (initialInvariant := headInvariant)
                    (initialBindersBelow := headBindersBelow)
                    (integerPatternsSubset := integerPatternsSubset)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    (retained := by
                      intro argument member
                      exact retained argument (by simp [member]))
                    (childrenRetained := by
                      intro argument member
                      exact childrenRetained argument (by simp [member]))
                    (covered := by
                      intro argument member
                      exact covered argument (by simp [member]))
                    (childSound := childSound)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Selected-call soundness with one whole-body, retention-aware recursive
boundary.  Candidate search does not allocate occurrences, so the actual
argument traversal remains the node source for recursive bases.  Delayed
argument coercions are handled only through scoped preservation and
requirement retention; no false append-only extension across attachment is
assumed. -/
theorem
    inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_under_scoped_retention_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState evidenceState :
      Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {resultState later : Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected
      argumentState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
    (argumentInitialReady : argumentInitial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentInitial.inference.next)
    (nodesBelow : argumentInitial.NodesBelowNextOccurrence)
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ evidenceState.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ evidenceState.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ evidenceState.requirements)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (argumentState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures =
      inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties
    argumentInitialReady signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      argumentProperties.1.next_le
  have argumentIdsUnique :=
    Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  obtain ⟨signature, _, _, canonical, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have retainedAtAttempt :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      argumentExpressionIds argumentIdsUnique evidenceArgumentNodesPreserved
  have candidateNodesEq : attempt.state.nodes = argumentState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have retainedAtArguments : ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember node requirement contains requirementMember
    apply retainedAtAttempt argument argumentMember
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ attempt.state.nodes
      rw [candidateNodesEq]
      exact member
    · exact requirementMember
  have bases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_retained_bounded
      (roots := roots) fuel_lt nodesBelow argumentIntegerPatternsSubset
      argumentIntegerSubset argumentRequirementsSubset retainedAtArguments
      childSound argumentsSuccess
  exact
    selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
      selectionSuccess recordEq candidatesSubset bases argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 signatureFormation
      functionsCanonical expectedAtArguments substitutionExtends
      requirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      contextValid signaturesEq traitSuccess profileSuccess traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

/-- Coverage-aware selected-call bridge used by the eventual closed mutual
fuel induction.  The selected attachment row identifies exactly the inferred
arguments, so its certified argument coverage is converted pointwise into the
coverage demanded by the recursive callback. -/
theorem
    inferExprsFuel_selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_under_covered_scoped_retention_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {argumentSources : List Syntax.Expr}
    {argumentInitial argumentState evidenceState :
      Frontend.SourceInference.State}
    {arguments : List InferredExpression}
    {source callee : Syntax.Expr} {name : String}
    {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression}
    {resultState later : Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (argumentsSuccess : Detail.inferExprsFuel fuel inferenceContext
      argumentSources argumentInitial = .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates arguments integerLiteralOrigins call expected
      argumentState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name arguments attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
    (argumentInitialReady : argumentInitial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentInitial.inference.next)
    (nodesBelow : argumentInitial.NodesBelowNextOccurrence)
    (argumentInitialInvariant : ActiveLocalContextInvariant argumentInitial
      later.inference.substitution active)
    (argumentInitialBindersBelow :
      argumentInitial.LocalBindersBelowNextLocal)
    (argumentIntegerPatternsSubset :
      argumentState.integerPatterns ⊆ evidenceState.integerPatterns)
    (argumentIntegerSubset :
      argumentState.integerLiterals ⊆ evidenceState.integerLiterals)
    (argumentRequirementsSubset :
      argumentState.requirements ⊆ evidenceState.requirements)
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (argumentState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      (arguments.map (·.id))
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures =
      inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties
    argumentInitialReady signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow argumentState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      argumentProperties.1.next_le
  have argumentIdsUnique :=
    Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  obtain ⟨signature, _, _, canonical, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have retainedAtAttempt :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      argumentExpressionIds argumentIdsUnique evidenceArgumentNodesPreserved
  have candidateNodesEq : attempt.state.nodes = argumentState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have retainedAtArguments : ∀ argument ∈ arguments,
      ExpressionRequirementsRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember node requirement contains requirementMember
    apply retainedAtAttempt argument argumentMember
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ attempt.state.nodes
      rw [candidateNodesEq]
      exact member
    · exact requirementMember
  have childrenRetainedAtArguments : ∀ argument ∈ arguments,
      ExpressionDirectChildrenRetainedAt
        (argumentState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember
    have argumentToAttempt : ExpressionDirectChildrenRetainedAt
        (argumentState.toTypedSource roots) (attempt.state.toTypedSource roots)
        argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofNodesEq
      exact candidateNodesEq
    have attemptToAttached : ExpressionDirectChildrenRetainedAt
        (attempt.state.toTypedSource roots)
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots) argument.id :=
      ExpressionDirectChildrenRetainedAt.ofAttachExpressionCoercions
        attempt.state attempt.argumentCoercions roots argument.id
    have attachedToEvidence : ExpressionDirectChildrenRetainedAt
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots)
        evidenceSource argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt
        (substitution := later.inference.substitution)
      intro id node idMember contains
      simp only [List.mem_singleton] at idMember
      subst id
      apply evidenceArgumentNodesPreserved
      · exact List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
      · exact contains
    intro child edge
    exact attachedToEvidence (attemptToAttached (argumentToAttempt edge))
  have coveredArguments : ∀ argument ∈ arguments,
      TemplateScopeCovered evidenceSource active
        (.expression argument.id) := by
    intro argument argumentMember
    have argumentIdMember : argument.id ∈ arguments.map (·.id) :=
      List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
    have entryIdMember : argument.id ∈
        attempt.argumentCoercions.map (·.expression) := by
      rw [argumentExpressionIds]
      exact argumentIdMember
    obtain ⟨entry, entryMember, entryIdEq⟩ :=
      List.mem_map.mp entryIdMember
    simpa only [entryIdEq] using argumentCovered entry entryMember
  have bases :=
    inferExprsFuel_success_argumentTypingBasesValid_under_covered_retained_bounded
      (roots := roots) fuel_lt argumentInitialReady signatureFormation
      functionsCanonical nodesBelow argumentInitialInvariant
      argumentInitialBindersBelow argumentIntegerPatternsSubset
      argumentIntegerSubset argumentRequirementsSubset retainedAtArguments
      childrenRetainedAtArguments coveredArguments childSound argumentsSuccess
  exact
    selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
      selectionSuccess recordEq candidatesSubset bases argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 signatureFormation
      functionsCanonical expectedAtArguments substitutionExtends
      requirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      contextValid signaturesEq traitSuccess profileSuccess traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

/-- The four successful executable tails of a source call.  Constructor
discovery precedes ordinary call dispatch; a non-constructor call first
traverses its argument row and then records either a selected direct call, a
builtin call, or an indirect call through a recursively inferred callee. -/
inductive CallExpressionDispatchFacts
    (context : Frontend.SourceInference.Context)
    (source callee : Syntax.Expr)
    (arguments : Syntax.DelimitedList Syntax.Expr)
    (id : ExpressionId) (expected : Option TypeSystem.Ty)
    (fuel : Nat) (allocated : Frontend.SourceInference.State)
    (result : InferredExpression × Frontend.SourceInference.State) : Prop where
  | constructor
      {dataType : ProgramDataSignature}
      {constructor : ProgramDataConstructorSignature}
      {instantiation : DataConstructorInstantiation}
      {constructorState : Frontend.SourceInference.State}
      (discovery : Detail.constructorCalleeCandidates context allocated callee =
        .ok [(dataType, constructor)])
      (freshInstantiation :
        Detail.freshDataConstructorInstantiation dataType constructor allocated =
          (instantiation, constructorState))
      (application : Detail.inferConstructorApplicationFuel fuel context source
        id instantiation arguments.elements expected constructorState =
          .ok result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | selected
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {candidates : List ProgramFunctionSignature}
      {integerLiterals : List IntegerLiteralOrigin}
      {attempt : Detail.CandidateAttemptResult}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (candidateOrigin :
        SelectedCallCandidatesOrigin context name candidates)
      (selection : Detail.selectFunctionCandidateFrom context name candidates
        inferredArguments integerLiterals id expected argumentState =
          .ok attempt)
      (recording : Detail.recordSelectedCall source callee name
        inferredArguments attempt = result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | builtin
      {inferredArguments : List InferredExpression}
      {argumentState : Frontend.SourceInference.State}
      {name : String} {function : BuiltinFunctionId}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (recording : Detail.recordBuiltinFunctionCall source callee name function
        inferredArguments id expected argumentState = .ok result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result
  | indirect
      {inferredArguments : List InferredExpression}
      {argumentState calleeState : Frontend.SourceInference.State}
      {inferredCallee : InferredExpression}
      {application : Detail.IndirectApplicationResult}
      (argumentsSuccess : Detail.inferExprsFuel fuel context arguments.elements
        allocated = .ok (inferredArguments, argumentState))
      (calleeSuccess : Detail.inferExprFuel fuel context callee none
        argumentState = .ok (inferredCallee, calleeState))
      (applicationSuccess : Detail.applyFunctionType context id
        inferredCallee.type inferredArguments expected calleeState =
          .ok application)
      (recording : Detail.recordIndirectCall source inferredCallee
        inferredArguments application = result) :
      CallExpressionDispatchFacts context source callee arguments id expected
        fuel allocated result

/-- Invert a successful source call into the exact semantic tail executed by
the frontend. -/
theorem inferExprFuel_success_call_dispatch_facts
    {fuel : Nat}
    {context : Frontend.SourceInference.Context}
    {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : source.value = .call callee arguments)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context source expected initial =
      .ok result) :
    CallExpressionDispatchFacts context source callee arguments id expected
      fuel allocated result := by
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases discovery : Detail.constructorCalleeCandidates context allocated callee with
  | error error =>
      simp [discovery] at success
  | ok candidates =>
      cases candidates with
      | nil =>
          simp only [discovery] at success
          repeat' first | split at success
          all_goals
            try simp_all [pure, Pure.pure, Except.pure]
          all_goals
            first
            | apply CallExpressionDispatchFacts.indirect <;> assumption
            | apply CallExpressionDispatchFacts.builtin <;> assumption
            | apply CallExpressionDispatchFacts.selected
              · assumption
              · first
                | apply SelectedCallCandidatesOrigin.qualified <;> assumption
                | apply SelectedCallCandidatesOrigin.unqualified <;> assumption
              · assumption
              · assumption
      | cons first rest =>
          rcases first with ⟨dataType, constructor⟩
          cases rest with
          | nil =>
              simp only [discovery] at success
              generalize freshEq :
                Detail.freshDataConstructorInstantiation dataType constructor
                  allocated = pair at success
              rcases pair with ⟨instantiation, constructorState⟩
              exact .constructor discovery freshEq success
          | cons second tail =>
              simp [discovery] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
