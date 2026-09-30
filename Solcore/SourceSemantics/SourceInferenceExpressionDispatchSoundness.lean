import Solcore.SourceSemantics.SourceInferenceExpressionSoundness

/-!
Operational provenance for the recursive children of expression inference.

The eventual expression dispatcher must not ask for soundness of an
unrelated successful `inferExprFuel` computation.  Its recursive boundary is
therefore indexed by the enclosing fuel and tied to the enclosing node source
and evidence state by explicit source-extension and ledger-subset proofs.

This module first supplies the two source-ordered child traversals used by the
non-lambda expression branches: ordinary expression lists (tuples and call
arguments) and constructor arguments.  Both theorems construct every child
request from the successful traversal which actually produced it.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- A recursive expression computation together with the operational facts
which relate it to one enclosing expression proof.

`sourceExtension` is deliberately an extension of the unsubstituted node
table.  It both certifies that the child belongs to the enclosing traversal
and lets an induction hypothesis weaken the child's typing base into the
parent's node source.  The two subset fields perform the analogous job for
the final integer-literal and requirement ledgers. -/
structure ExpressionChildInferenceProvenance
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (roots : List NodeId) where
  fuel : Nat
  expression : Syntax.Expr
  expected : Option TypeSystem.Ty
  initial : Frontend.SourceInference.State
  final : Frontend.SourceInference.State
  inferred : InferredExpression
  fuel_lt : fuel < parentFuel
  initialNodesBelow : initial.NodesBelowNextOccurrence
  success : Detail.inferExprFuel fuel inferenceContext expression expected
    initial = .ok (inferred, final)
  sourceExtension : TypingSourceExtends (final.toTypedSource roots)
    ambientNodeSource
  integerLiteralsSubset :
    final.integerLiterals ⊆ evidenceState.integerLiterals
  requirementsSubset : final.requirements ⊆ evidenceState.requirements

/-- The recursive semantic boundary used by the expression dispatcher.
Unlike an unqualified callback over arbitrary successful child inference,
each invocation carries a fuel decrease and concrete source/ledger links to
the enclosing computation. -/
def ExpressionChildTypingCallback
    (parentFuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (ambientNodeSource semanticSource : TypedSource)
    (evidenceState : Frontend.SourceInference.State)
    (context : SourceSemantics.Context)
    (substitution : TypeSystem.Substitution)
    (roots : List NodeId) : Prop :=
  ∀ child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      ambientNodeSource evidenceState roots,
    ExpressionTypingBase (child.final.toTypedSource roots) semanticSource
      context substitution child.inferred

/-- Close one provenance-indexed recursive expression result against the
shared finalization resources.  Keeping this adapter at the child boundary
avoids repeating the node-source weakening and the source-context side
conditions in every expression-form branch. -/
theorem FinalInferenceResources.expressionHasType_of_childProvenance
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots
      result)
    {parentFuel : Nat}
    {active sourceContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (state.toTypedSource roots) result.typedSource state active
      result.substitution roots)
    (child : ExpressionChildInferenceProvenance parentFuel inferenceContext
      (state.toTypedSource roots) state roots)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      result.substitution closedVariables sourceContext active) :
    ExpressionHasType result.typedSource active child.inferred.id
      (result.substitution.apply child.inferred.type) := by
  exact resources.expressionHasType_of_typingBase
    ((childSound child).weakenNodeSource child.sourceExtension.nodes_prefix)
    binders signaturesEq parametersEq ownerEq residual contextValid

/-- Finalization closes argument bases which were built in any exact prefix
of its input node table. -/
theorem FinalInferenceResources.expressionsHaveTypes_of_argumentTypingBases_prefix
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots
      result)
    {nodeSource : TypedSource}
    {active sourceContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    {arguments : List InferredExpression}
    (bases : ArgumentTypingBasesValid nodeSource result.typedSource active
      result.substitution arguments)
    (extension : TypingSourceExtends nodeSource (state.toTypedSource roots))
    (binders : TypeParameterBindersWellFormed sourceContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      result.substitution closedVariables sourceContext active) :
    ExpressionsHaveTypes result.typedSource active
      (arguments.map (·.id))
      (arguments.map fun argument =>
        result.substitution.apply argument.type) := by
  exact resources.expressionsHaveTypes_of_argumentTypingBases
    (bases.weakenNodeSource extension.nodes_prefix) binders signaturesEq
      parametersEq ownerEq residual contextValid

private theorem recordExpressionWithExpected_success_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    initial.nodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have fittedPrefix : initial.nodes <+: fitted.state.nodes := by
    rw [(Detail.withExpected_occurrenceState_eq fittedSuccess).1]
    exact List.prefix_rfl
  rw [resultStateEq]
  exact fittedPrefix.trans
    (Frontend.SourceInference.State.recordNode_nodesPrefix fitted.state _)

private theorem fresh_eq_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final))
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  exact .refl _

private theorem fresh_eq_integerLiterals_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.integerLiterals = initial.integerLiterals := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem fresh_eq_requirements_eq
    {initial final : Frontend.SourceInference.State}
    {type : TypeSystem.Ty}
    (success : initial.fresh = (type, final)) :
    final.requirements = initial.requirements := by
  have finalEq : initial.fresh.2 = final := congrArg Prod.snd success
  rw [← finalEq]
  rfl

private theorem unify_success_typingSourceExtends
    {initial final : Frontend.SourceInference.State}
    {left right : TypeSystem.Ty}
    (success : Detail.unify initial left right = .ok final)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · change final.owner = initial.owner
    have headerEq := Detail.unify_state_header success
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  · change initial.nodes <+: final.nodes
    rw [(Detail.unify_occurrenceState_eq success).1]
    exact List.prefix_rfl

private theorem inferExprsFuel_success_owner_eq
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final)) :
    final.owner = initial.owner := by
  induction fuel generalizing expressions initial inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          cases success.2
          rfl
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
                  exact (induction tailSuccess).trans
                    (Detail.inferExprFuel_preserves_owner headSuccess)

/-- Ordinary expression-list inference is append-only when its input node
table is protected by the occurrence allocator bound. -/
theorem inferExprsFuel_success_typingSourceExtends_under_bound
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    (success : Detail.inferExprsFuel fuel inferenceContext expressions initial =
      .ok (inferred, final))
    (below : initial.NodesBelowNextOccurrence)
    (roots : List NodeId := []) :
    TypingSourceExtends (initial.toTypedSource roots)
      (final.toTypedSource roots) := by
  constructor
  · exact inferExprsFuel_success_owner_eq success
  · exact Detail.inferExprsFuel_preserves_nodesPrefix success
      (nodesPrefix := List.prefix_rfl)
      (baseBelow := below)
      (cutoffLe := Nat.le_refl _)

/-- Source-ordered ordinary expression-list inference builds argument typing
bases under a fixed enclosing source.  Every recursive callback invocation is
the actual head step exposed by the successful list traversal; the tail
execution supplies its child-to-parent source extension and ledger subsets. -/
theorem
    inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {ambientNodeSource semanticSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultExtension : TypingSourceExtends (final.toTypedSource roots)
      ambientNodeSource)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      ambientNodeSource semanticSource evidenceState target outer roots)
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
                      tailSuccess
                      headBelow roots
                  have headExtension : TypingSourceExtends
                      (headState.toTypedSource roots) ambientNodeSource :=
                    TypingSourceExtends.trans headToFinal resultExtension
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_integerLiterals_subset tailSuccess)
                      integerLiteralsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferExprsFuel_requirements_subset tailSuccess)
                      requirementsSubset
                  have headBase := childSound {
                    fuel := fuel
                    expression
                    expected := none
                    initial
                    final := headState
                    inferred := head
                    fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headExtension
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (fuel_lt := Nat.lt_trans (Nat.lt_succ_self fuel) fuel_lt)
                    (initialBelow := headBelow)
                    (resultExtension := resultExtension)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Constructor-argument traversal has structural rather than fuel recursion,
but every expression child still runs at fuel strictly below the enclosing
expression.  As above, the remaining tail is used to derive the concrete
child-to-parent source extension and both evidence-ledger inclusions. -/
theorem
    inferConstructorArgumentsFuel_success_argumentTypingBasesValid_under_ambient_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {sources : List Syntax.Expr} {expectedTypes : List TypeSystem.Ty}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {ambientNodeSource semanticSource : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (roots : List NodeId := [])
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultExtension : TypingSourceExtends (final.toTypedSource roots)
      ambientNodeSource)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      ambientNodeSource semanticSource evidenceState target outer roots)
    (success : Detail.inferConstructorArgumentsFuel fuel inferenceContext
      sources expectedTypes initial = .ok (inferred, final)) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource target
      outer inferred := by
  induction sources generalizing expectedTypes initial inferred final with
  | nil =>
      cases expectedTypes with
      | nil =>
          simp only [Detail.inferConstructorArgumentsFuel, pure, Pure.pure,
            Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expected expectedTypes =>
          simp [Detail.inferConstructorArgumentsFuel] at success
  | cons source sources induction =>
      cases expectedTypes with
      | nil =>
          simp [Detail.inferConstructorArgumentsFuel] at success
      | cons expected expectedTypes =>
          unfold Detail.inferConstructorArgumentsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext source
              (some (initial.resolve expected)) initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel
                  inferenceContext sources expectedTypes headState with
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
                    inferConstructorArgumentsFuel_success_typingSourceExtends
                      tailSuccess headBelow roots
                  have headExtension : TypingSourceExtends
                      (headState.toTypedSource roots) ambientNodeSource :=
                    TypingSourceExtends.trans headToFinal resultExtension
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_integerLiterals_subset
                        tailSuccess)
                      integerLiteralsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆ evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_requirements_subset
                        tailSuccess)
                      requirementsSubset
                  have headBase := childSound {
                    fuel
                    expression := source
                    expected := some (initial.resolve expected)
                    initial
                    final := headState
                    inferred := head
                    fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headExtension
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have finalHead : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource target outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have tailBases := induction
                    (initialBelow := headBelow)
                    (resultExtension := resultExtension)
                    (integerLiteralsSubset := integerLiteralsSubset)
                    (requirementsSubset := requirementsSubset)
                    tailSuccess
                  exact .cons finalHead tailBases

/-- Constructor arguments, closed directly in the final semantic source and
indexed by their declared payload types.  This is the bounded-provenance
replacement for the older local theorem whose child callback ranged over
unrelated successful expression computations. -/
theorem
    inferConstructorArgumentsFuel_success_expressionsHaveTypes_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {parentFuel fuel : Nat}
    {sources : List Syntax.Expr} {expectedTypes : List TypeSystem.Ty}
    {initial final : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expected ∈ expectedTypes,
      expected.VariablesBelow initial.inference.next)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (outerExtension : finalized.substitution.SemanticallyExtends
      final.inference.substitution)
    (resultExtension : TypingSourceExtends (final.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (evidenceState.toTypedSource roots) finalized.typedSource evidenceState
      active finalized.substitution roots)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (success : Detail.inferConstructorArgumentsFuel fuel inferenceContext
      sources expectedTypes initial = .ok (inferred, final)) :
    ExpressionsHaveTypes finalized.typedSource active
      (inferred.map (·.id)) (expectedTypes.map finalized.substitution.apply) := by
  induction sources generalizing expectedTypes initial inferred final with
  | nil =>
      cases expectedTypes with
      | nil =>
          simp only [Detail.inferConstructorArgumentsFuel, pure, Pure.pure,
            Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil active
      | cons expected expectedTypes =>
          simp [Detail.inferConstructorArgumentsFuel] at success
  | cons source sources induction =>
      cases expectedTypes with
      | nil =>
          simp [Detail.inferConstructorArgumentsFuel] at success
      | cons expected expectedTypes =>
          unfold Detail.inferConstructorArgumentsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext source
              (some (initial.resolve expected)) initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel
                  inferenceContext sources expectedTypes headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have expectedHeadBelow :
                      expected.VariablesBelow initial.inference.next :=
                    expectedBelow expected (by simp)
                  have resolvedHeadBelow :
                      (initial.resolve expected).VariablesBelow
                        initial.inference.next :=
                    ready.solved.variablesBelow_apply expectedHeadBelow
                  have headProperties :=
                    Detail.inferExprFuel_inferenceProperties ready
                      signatureFormation functionsCanonical (by
                        intro candidate member
                        simp only [Option.mem_def] at member
                        injection member with candidateEq
                        subst candidate
                        exact resolvedHeadBelow) headSuccess
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have tailExpectedBelow : ∀ candidate ∈ expectedTypes,
                      candidate.VariablesBelow headState.inference.next := by
                    intro candidate member
                    exact (expectedBelow candidate (by simp [member])).weaken
                      headProperties.1.next_le
                  have tailProperties :=
                    Detail.inferConstructorArgumentsFuel_inferenceProperties
                      headProperties.2.1 signatureFormation functionsCanonical
                      tailExpectedBelow tailSuccess
                  have outerHead : finalized.substitution.SemanticallyExtends
                      headState.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans
                      outerExtension tailProperties.1.substitution_extends
                  have outerInitial :
                      finalized.substitution.SemanticallyExtends
                        initial.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans outerHead
                      headProperties.1.substitution_extends
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferConstructorArgumentsFuel_success_typingSourceExtends
                      tailSuccess headBelow roots
                  have headToEvidence : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (evidenceState.toTypedSource roots) :=
                    TypingSourceExtends.trans headToFinal resultExtension
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_integerLiterals_subset
                        tailSuccess)
                      integerLiteralsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆
                        evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_requirements_subset
                        tailSuccess)
                      requirementsSubset
                  have headBase := childSound {
                    fuel
                    expression := source
                    expected := some (initial.resolve expected)
                    initial
                    final := headState
                    inferred := head
                    fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToEvidence
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headType : ExpressionHasType finalized.typedSource active
                      head.id (finalized.substitution.apply head.type) :=
                    resources.expressionHasType_of_typingBase
                      (headBase.weakenNodeSource headToEvidence.nodes_prefix)
                      sourceBinders signaturesEq parametersEq ownerEq residual
                      contextValid
                  have headExpectedEq : finalized.substitution.apply head.type =
                      finalized.substitution.apply expected := by
                    calc
                      finalized.substitution.apply head.type =
                          finalized.substitution.apply
                            (initial.resolve expected) :=
                        Detail.inferExprFuel_expected_type_apply_eq headSuccess
                          outerHead
                      _ = finalized.substitution.apply expected := by
                        simpa [Frontend.SourceInference.State.resolve,
                          TypeSystem.InferState.resolve] using
                            outerInitial expected
                  have headExpected : ExpressionHasType finalized.typedSource
                      active head.id
                      (finalized.substitution.apply expected) := by
                    rw [← headExpectedEq]
                    exact headType
                  have tailTyping := induction
                    headProperties.2.1 tailExpectedBelow headBelow
                    outerExtension resultExtension integerLiteralsSubset
                    requirementsSubset tailSuccess
                  exact .cons headExpected tailTyping

/-- The nonrecursive recording tail shared by constructor branches.  Child
traversal and provenance have already been discharged into `argumentsType`. -/
theorem
    recordExpressionWithExpected_success_constructor_expressionTypingBase_scoped
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List InferredExpression}
    {expected : Option TypeSystem.Ty}
    {argumentState resultState later : Frontend.SourceInference.State}
    {result : InferredExpression}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {ledgerSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      source id (argumentState.resolve instantiation.resultType)
      (.constructor instantiation (arguments.map (·.id))) [] expected
      argumentState none = .ok (result, resultState))
    (outerArguments : later.inference.substitution.SemanticallyExtends
      argumentState.inference.substitution)
    (argumentsType : ExpressionsHaveTypes ledgerSource active
      (arguments.map (·.id))
      (instantiation.payloadTypes.map later.inference.substitution.apply))
    (binders : TypeParameterBindersWellFormed active)
    (instantiationValid :
      SourceSemantics.DataConstructorInstantiation.Admissible active
        (instantiation.applySubstitution later.inference.substitution))
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (sourceExtension : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution) ledgerSource)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) ledgerSource active
      later.inference.substitution result := by
  have rawTypeEq : later.inference.substitution.apply
      (argumentState.resolve instantiation.resultType) =
      later.inference.substitution.apply instantiation.resultType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        outerArguments instantiation.resultType
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply
        (argumentState.resolve instantiation.resultType)) := by
    rw [rawTypeEq]
    simpa [DataConstructorInstantiation.applySubstitution] using
      (SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
        binders instantiationValid)
  have formType : ExpressionFormHasRawType ledgerSource active
      ((.constructor instantiation
          (arguments.map (·.id)) : ExpressionForm).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply
        (argumentState.resolve instantiation.resultType))
      (.ordinary []) := by
    rw [rawTypeEq]
    simpa [ExpressionForm.applySubstitution,
      DataConstructorInstantiation.applySubstitution] using
        (ExpressionFormHasRawType.constructor instantiationValid
          argumentsType)
  exact recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped
    recordSuccess substitutionExtends requirementsSubset sourceExtension
    formType rawAdmissible traitSuccess profileSuccess catalog contextValid
    signaturesEq traitName solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered

/-- Constructor application soundness with a child callback tied to the
enclosing expression's final node source and evidence ledgers.  The optional
expected-type unification is handled before the argument traversal; every
actual argument step is then discharged by the bounded constructor-list
theorem above. -/
theorem
    inferConstructorApplicationFuel_success_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {parentFuel fuel : Nat}
    {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial resultState : Frontend.SourceInference.State}
    {result : InferredExpression}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (success : Detail.inferConstructorApplicationFuel fuel inferenceContext
      source id instantiation arguments expected initial =
        .ok (result, resultState))
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (payloadBelow : ∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow
      initial.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (resultState.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentIntegerLiteralsSubset :
      resultState.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      resultState.requirements ⊆ evidenceState.requirements)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (childSound : ExpressionChildTypingCallback parentFuel inferenceContext
      (evidenceState.toTypedSource roots) finalized.typedSource evidenceState
      active finalized.substitution roots)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (activeBinders : TypeParameterBindersWellFormed active)
    (instantiationValid :
      SourceSemantics.DataConstructorInstantiation.Admissible active
        (instantiation.applySubstitution finalized.substitution))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots)
      finalized.typedSource active finalized.substitution result := by
  have wholeSuccess := success
  have parentToSemantic : TypingSourceExtends
      ((resultState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        resultState.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      resultState.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  have finish
      {argumentInitial argumentsState : Frontend.SourceInference.State}
      {inferredArguments : List InferredExpression}
      (argumentInitialReady : argumentInitial.InferenceReady)
      (payloadAtArgumentInitial : ∀ payload ∈ instantiation.payloadTypes,
        payload.VariablesBelow argumentInitial.inference.next)
      (resultAtArgumentInitial : instantiation.resultType.VariablesBelow
        argumentInitial.inference.next)
      (expectedAtArgumentInitial : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow argumentInitial.inference.next)
      (nodesAtArgumentInitial : argumentInitial.NodesBelowNextOccurrence)
      (argumentInitialOwner : argumentInitial.owner = initial.owner)
      (argumentsSuccess : Detail.inferConstructorArgumentsFuel fuel
        inferenceContext arguments instantiation.payloadTypes argumentInitial =
          .ok (inferredArguments, argumentsState))
      (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
        source id (argumentsState.resolve instantiation.resultType)
        (.constructor instantiation (inferredArguments.map (·.id))) []
        expected argumentsState none = .ok (result, resultState)) :
      ExpressionTypingBase (resultState.toTypedSource roots)
        finalized.typedSource active finalized.substitution result := by
    have argumentsProperties :=
      Detail.inferConstructorArgumentsFuel_inferenceProperties
        argumentInitialReady signatureFormation functionsCanonical
        payloadAtArgumentInitial argumentsSuccess
    have resultAtArguments : instantiation.resultType.VariablesBelow
        argumentsState.inference.next :=
      resultAtArgumentInitial.weaken argumentsProperties.1.next_le
    have resolvedResultBelow :
        (argumentsState.resolve instantiation.resultType).VariablesBelow
          argumentsState.inference.next :=
      argumentsProperties.2.1.solved.variablesBelow_apply resultAtArguments
    have expectedAtArguments : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow argumentsState.inference.next := by
      intro expectedType member
      exact (expectedAtArgumentInitial expectedType member).weaken
        argumentsProperties.1.next_le
    have recordProperties :=
      Detail.recordExpressionWithExpected_inferenceProperties
        argumentsProperties.2.1 resolvedResultBelow expectedAtArguments
        recordSuccess
    have outerArguments : finalized.substitution.SemanticallyExtends
        argumentsState.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
        recordProperties.1.substitution_extends
    have argumentsOwner : argumentsState.owner = argumentInitial.owner :=
      Detail.inferConstructorArgumentsFuel_preserves_owner argumentsSuccess
    have resultOwner : resultState.owner = initial.owner :=
      Detail.inferConstructorApplicationFuel_preserves_owner wholeSuccess
    have argumentsToResult : TypingSourceExtends
        (argumentsState.toTypedSource roots)
        (resultState.toTypedSource roots) := by
      constructor
      · exact resultOwner.trans
          (argumentInitialOwner.symm.trans argumentsOwner.symm)
      · exact recordExpressionWithExpected_success_nodesPrefix recordSuccess
    have argumentsToEvidence : TypingSourceExtends
        (argumentsState.toTypedSource roots)
        (evidenceState.toTypedSource roots) :=
      TypingSourceExtends.trans argumentsToResult parentExtension
    have argumentsIntegerLiteralsSubset :
        argumentsState.integerLiterals ⊆ evidenceState.integerLiterals := by
      intro origin member
      apply parentIntegerLiteralsSubset
      rw [Detail.recordExpressionWithExpected_integerLiterals_eq recordSuccess]
      exact member
    have argumentsRequirementsSubset :
        argumentsState.requirements ⊆ evidenceState.requirements :=
      List.Subset.trans
        (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
        parentRequirementsSubset
    have argumentsType : ExpressionsHaveTypes finalized.typedSource active
        (inferredArguments.map (·.id))
        (instantiation.payloadTypes.map finalized.substitution.apply) :=
      inferConstructorArgumentsFuel_success_expressionsHaveTypes_under_ambient_bounded
        resources fuel_lt argumentInitialReady signatureFormation
        functionsCanonical payloadAtArgumentInitial nodesAtArgumentInitial
        outerArguments argumentsToEvidence argumentsIntegerLiteralsSubset
        argumentsRequirementsSubset childSound sourceBinders signaturesEq
        parametersEq ownerEq residual contextValid argumentsSuccess
    simpa only [← resources.substitution_eq] using
      (recordExpressionWithExpected_success_constructor_expressionTypingBase_scoped
        (later := resources.finalState)
        (base := finalizedRequirementContext inferenceContext finalized)
        recordSuccess
        (by simpa only [← resources.substitution_eq] using outerArguments)
        (by simpa only [← resources.substitution_eq] using argumentsType)
        activeBinders
        (by simpa only [← resources.substitution_eq] using
          instantiationValid)
        finalSubstitutionExtends finalRequirementsSubset
        (by simpa only [← resources.substitution_eq] using parentToSemantic)
        traitSuccess profileSuccess catalog finalContextValid signaturesEq
        traitName resources.solve_success resources.solved_context_eq
        resources.ledger resources.ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered)
  unfold Detail.inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity] at success
    cases expected with
    | none =>
        simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
        cases argumentsResult : Detail.inferConstructorArgumentsFuel fuel
            inferenceContext arguments instantiation.payloadTypes initial with
        | error error =>
            simp [argumentsResult] at success
        | ok argumentsPair =>
            rcases argumentsPair with ⟨inferredArguments, argumentsState⟩
            simp only [argumentsResult] at success
            exact finish ready payloadBelow resultBelow expectedBelow nodesBelow
              rfl argumentsResult success
    | some expectedType =>
        cases unifyResult : Detail.unify initial instantiation.resultType
            expectedType with
        | error error =>
            simp [unifyResult, bind, Except.bind] at success
        | ok argumentInitial =>
            simp only [unifyResult, bind, Except.bind] at success
            have expectedTypeBelow : expectedType.VariablesBelow
                initial.inference.next :=
              expectedBelow expectedType (by simp)
            have unifyProgress := Detail.unify_inferenceProgress ready.solved
              resultBelow expectedTypeBelow unifyResult
            have argumentInitialReady :=
              Detail.unify_preserves_inferenceReady ready resultBelow
                expectedTypeBelow unifyResult
            have payloadAtArgumentInitial : ∀ payload ∈
                instantiation.payloadTypes,
                payload.VariablesBelow argumentInitial.inference.next := by
              intro payload member
              exact (payloadBelow payload member).weaken unifyProgress.next_le
            have resultAtArgumentInitial :
                instantiation.resultType.VariablesBelow
                  argumentInitial.inference.next :=
              resultBelow.weaken unifyProgress.next_le
            have expectedAtArgumentInitial : ∀ candidate ∈
                (some expectedType : Option TypeSystem.Ty),
                candidate.VariablesBelow argumentInitial.inference.next := by
              intro candidate member
              simp only [Option.mem_def] at member
              injection member with candidateEq
              subst candidate
              exact expectedTypeBelow.weaken unifyProgress.next_le
            have nodesAtArgumentInitial :
                argumentInitial.NodesBelowNextOccurrence :=
              (Detail.unify_occurrenceBoundExtends unifyResult
                ).nodesBelowNextOccurrence nodesBelow
            have argumentInitialOwner :
                argumentInitial.owner = initial.owner :=
              congrArg (fun header : Frontend.SourceInference.State.Header =>
                header.owner) (Detail.unify_state_header unifyResult)
            cases argumentsResult : Detail.inferConstructorArgumentsFuel fuel
                inferenceContext arguments instantiation.payloadTypes
                argumentInitial with
            | error error =>
                simp [argumentsResult] at success
            | ok argumentsPair =>
                rcases argumentsPair with
                  ⟨inferredArguments, argumentsState⟩
                simp only [argumentsResult] at success
                exact finish argumentInitialReady payloadAtArgumentInitial
                  resultAtArgumentInitial expectedAtArgumentInitial
                  nodesAtArgumentInitial argumentInitialOwner argumentsResult
                  success
  · simp [arity, bind, Except.bind] at success

/-- The grouping branch obtains its sole recursive premise from the actual
inner-expression trace and transports it through the final group recording. -/
theorem inferExprFuel_success_group_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression inner : Syntax.Expr}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .group inner)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentIntegerLiteralsSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  obtain ⟨innerResult, innerState, innerSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_group_facts expressionEq allocationEq success
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [stateEq] using nextBelow
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have innerOwner : innerState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner innerSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have innerToParent : TypingSourceExtends
      (innerState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans (allocatedOwner.symm.trans innerOwner.symm)
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have innerToEvidence : TypingSourceExtends
      (innerState.toTypedSource roots) (evidenceState.toTypedSource roots) :=
    TypingSourceExtends.trans innerToParent parentExtension
  have innerIntegerLiteralsSubset :
      innerState.integerLiterals ⊆ evidenceState.integerLiterals := by
    intro origin member
    apply parentIntegerLiteralsSubset
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have innerRequirementsSubset :
      innerState.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recorded)
      parentRequirementsSubset
  have innerBase := childSound {
    fuel
    expression := inner
    expected
    initial := allocated
    final := innerState
    inferred := innerResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := innerSuccess
    sourceExtension := innerToEvidence
    integerLiteralsSubset := innerIntegerLiteralsSubset
    requirementsSubset := innerRequirementsSubset
  }
  have innerType : ExpressionHasType finalized.typedSource active
      innerResult.id (finalized.substitution.apply innerResult.type) :=
    resources.expressionHasType_of_typingBase
      (innerBase.weakenNodeSource innerToEvidence.nodes_prefix) sourceBinders
      signaturesEq parametersEq ownerEq residual contextValid
  have formType : ExpressionFormHasRawType finalized.typedSource active
      ((ExpressionForm.group innerResult.id).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply innerResult.type) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.group innerType
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      recorded finalSubstitutionExtends finalRequirementsSubset retained
      (by simpa only [← resources.substitution_eq] using formType)
      (by simpa only [← resources.substitution_eq] using
        innerType.type_admissible)
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

/-- The non-recursive proxy branch can be closed directly against the common
finalization input.  Its only operational provenance is the parent result's
source extension and requirement-ledger inclusion. -/
theorem inferExprFuel_success_proxy_expressionTypingBase_under_ambient
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression : Syntax.Expr} {marker : Syntax.SourceSpan}
    {sourceType : Syntax.TypeExpr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .proxy marker sourceType)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferExprFuel_success_proxy_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      (semanticSource := finalized.typedSource)
      (evidenceSource := finalized.typedSource)
      expressionEq allocationEq success finalSubstitutionExtends
      finalRequirementsSubset retained canonical parametersEq ownerEq
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

/-- The builtin-Boolean identifier branch has no recursive child and closes
against the same ambient finalization links as the proxy branch. -/
theorem
    inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_under_ambient
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (isBoolean :
      (name.value == "true" || name.value == "false") = true)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (activeBinders : TypeParameterBindersWellFormed active)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      (semanticSource := finalized.typedSource)
      (evidenceSource := finalized.typedSource)
      expressionEq allocationEq lookupEq isBoolean success
      finalSubstitutionExtends finalRequirementsSubset retained activeBinders
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

/-- Conditional inference exposes exactly its condition and two branch
computations to the bounded recursive callback.  The operational trace
supplies the source and ledger links for each of those three children. -/
theorem
    inferExprFuel_success_conditional_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression condition thenBranch elseBranch : Syntax.Expr}
    {question colon : Syntax.SourceSpan}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value =
      .conditional condition question thenBranch colon elseBranch)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (allocatedReady : allocated.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentIntegerLiteralsSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult,
      elseState, unifiedState, conditionSuccess, thenSuccess, elseSuccess,
      unifySuccess, recorded⟩ :=
    Detail.inferExprFuel_success_conditional_facts expressionEq allocationEq
      success
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [stateEq] using nextBelow
  have conditionBelow : conditionState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have thenBelow : thenState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence conditionBelow
  have elseBelow : elseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends elseSuccess
      ).nodesBelowNextOccurrence thenBelow
  have unifiedBelow : unifiedState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends unifySuccess
      ).nodesBelowNextOccurrence elseBelow
  have conditionToThen :=
    inferExprFuel_success_typingSourceExtends thenSuccess conditionBelow roots
  have thenToElse :=
    inferExprFuel_success_typingSourceExtends elseSuccess thenBelow roots
  have elseToUnified : TypingSourceExtends
      (elseState.toTypedSource roots) (unifiedState.toTypedSource roots) := by
    constructor
    · change unifiedState.owner = elseState.owner
      have headerEq := Detail.unify_state_header unifySuccess
      simpa [Frontend.SourceInference.State.header] using
        congrArg Frontend.SourceInference.State.Header.owner headerEq
    · change elseState.nodes <+: unifiedState.nodes
      rw [(Detail.unify_occurrenceState_eq unifySuccess).1]
      exact List.prefix_rfl
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have conditionOwner : conditionState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner conditionSuccess
  have thenOwner : thenState.owner = conditionState.owner :=
    Detail.inferExprFuel_preserves_owner thenSuccess
  have elseOwner : elseState.owner = thenState.owner :=
    Detail.inferExprFuel_preserves_owner elseSuccess
  have unifiedOwner : unifiedState.owner = elseState.owner := by
    have headerEq := Detail.unify_state_header unifySuccess
    simpa [Frontend.SourceInference.State.header] using
      congrArg Frontend.SourceInference.State.Header.owner headerEq
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have unifiedToParent : TypingSourceExtends
      (unifiedState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (conditionOwner.symm.trans
            (thenOwner.symm.trans
              (elseOwner.symm.trans unifiedOwner.symm))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have conditionToParent :=
    TypingSourceExtends.trans conditionToThen
      (TypingSourceExtends.trans thenToElse
        (TypingSourceExtends.trans elseToUnified unifiedToParent))
  have thenToParent :=
    TypingSourceExtends.trans thenToElse
      (TypingSourceExtends.trans elseToUnified unifiedToParent)
  have elseToParent :=
    TypingSourceExtends.trans elseToUnified unifiedToParent
  have conditionToEvidence :=
    TypingSourceExtends.trans conditionToParent parentExtension
  have thenToEvidence :=
    TypingSourceExtends.trans thenToParent parentExtension
  have elseToEvidence :=
    TypingSourceExtends.trans elseToParent parentExtension
  have unifiedIntegerLiteralsSubset :
      unifiedState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have elseIntegerLiteralsSubset :
      elseState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    apply unifiedIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have thenIntegerLiteralsSubset :
      thenState.integerLiterals ⊆ result.2.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset elseSuccess)
      elseIntegerLiteralsSubset
  have conditionIntegerLiteralsSubset :
      conditionState.integerLiterals ⊆ result.2.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset thenSuccess)
      thenIntegerLiteralsSubset
  have unifiedRequirementsSubset :
      unifiedState.requirements ⊆ result.2.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have elseRequirementsSubset :
      elseState.requirements ⊆ result.2.requirements := by
    intro requirement member
    apply unifiedRequirementsSubset
    rw [Detail.unify_requirements_eq unifySuccess]
    exact member
  have thenRequirementsSubset :
      thenState.requirements ⊆ result.2.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset elseSuccess)
      elseRequirementsSubset
  have conditionRequirementsSubset :
      conditionState.requirements ⊆ result.2.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset thenSuccess)
      thenRequirementsSubset
  let conditionChild : ExpressionChildInferenceProvenance (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots) evidenceState roots := {
    fuel
    expression := condition
    expected := some .bool
    initial := allocated
    final := conditionState
    inferred := conditionResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := conditionSuccess
    sourceExtension := conditionToEvidence
    integerLiteralsSubset := List.Subset.trans
      conditionIntegerLiteralsSubset parentIntegerLiteralsSubset
    requirementsSubset := List.Subset.trans conditionRequirementsSubset
      parentRequirementsSubset
  }
  let thenChild : ExpressionChildInferenceProvenance (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots) evidenceState roots := {
    fuel
    expression := thenBranch
    expected
    initial := conditionState
    final := thenState
    inferred := thenResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := conditionBelow
    success := thenSuccess
    sourceExtension := thenToEvidence
    integerLiteralsSubset := List.Subset.trans
      thenIntegerLiteralsSubset parentIntegerLiteralsSubset
    requirementsSubset := List.Subset.trans thenRequirementsSubset
      parentRequirementsSubset
  }
  let elseChild : ExpressionChildInferenceProvenance (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots) evidenceState roots := {
    fuel
    expression := elseBranch
    expected
    initial := thenState
    final := elseState
    inferred := elseResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := thenBelow
    success := elseSuccess
    sourceExtension := elseToEvidence
    integerLiteralsSubset := List.Subset.trans
      elseIntegerLiteralsSubset parentIntegerLiteralsSubset
    requirementsSubset := List.Subset.trans elseRequirementsSubset
      parentRequirementsSubset
  }
  have conditionTypeRaw := resources.expressionHasType_of_childProvenance
    childSound conditionChild sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have thenTypeRaw := resources.expressionHasType_of_childProvenance
    childSound thenChild sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have elseTypeRaw := resources.expressionHasType_of_childProvenance
    childSound elseChild sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = .bool :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      change TypeSystem.Ty.VariablesBelow allocated.inference.next
        (.constructor (.builtin .bool))
      exact TypeSystem.Ty.variablesBelow_constructor _ _) conditionSuccess
  have expectedAtCondition : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow conditionState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      conditionProperties.1.next_le
  have thenProperties := Detail.inferExprFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
      expectedAtCondition thenSuccess
  have expectedAtThen : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow thenState.inference.next := by
    intro expectedType member
    exact (expectedAtCondition expectedType member).weaken
      thenProperties.1.next_le
  have elseProperties := Detail.inferExprFuel_inferenceProperties
    thenProperties.2.1 signatureFormation functionsCanonical expectedAtThen
      elseSuccess
  have thenAtElse : thenResult.type.VariablesBelow
      elseState.inference.next :=
    thenProperties.2.2.weaken elseProperties.1.next_le
  have unifyProgress := Detail.unify_inferenceProgress
    elseProperties.2.1.solved thenAtElse elseProperties.2.2 unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    elseProperties.2.1 thenAtElse elseProperties.2.2 unifySuccess
  have allocatedToUnified : allocated.InferenceProgress unifiedState :=
    conditionProperties.1.trans
      (thenProperties.1.trans (elseProperties.1.trans unifyProgress))
  have expectedAtUnified : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow unifiedState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      allocatedToUnified.next_le
  have thenAtUnified : thenResult.type.VariablesBelow
      unifiedState.inference.next :=
    thenAtElse.weaken unifyProgress.next_le
  have resolvedThenBelow :
      (unifiedState.resolve thenResult.type).VariablesBelow
        unifiedState.inference.next :=
    unifiedReady.solved.variablesBelow_apply thenAtUnified
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties unifiedReady
      resolvedThenBelow expectedAtUnified recorded
  have finalUnified : finalized.substitution.SemanticallyExtends
      unifiedState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordedProperties.1.substitution_extends
  have finalElse : finalized.substitution.SemanticallyExtends
      elseState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans finalUnified
      unifyProgress.substitution_extends
  have finalThen : finalized.substitution.SemanticallyExtends
      thenState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans finalElse
      elseProperties.1.substitution_extends
  have finalCondition : finalized.substitution.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans finalThen
      thenProperties.1.substitution_extends
  have conditionEq : finalized.substitution.apply conditionResult.type =
      .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      finalCondition
  have conditionType : ExpressionHasType finalized.typedSource active
      conditionResult.id .bool := by
    rw [← conditionEq]
    exact conditionTypeRaw
  have resolvedThenEq :
      finalized.substitution.apply
          (unifiedState.resolve thenResult.type) =
        finalized.substitution.apply thenResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using finalUnified thenResult.type
  have resolvedElseEq :
      finalized.substitution.apply
          (unifiedState.resolve elseResult.type) =
        finalized.substitution.apply elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using finalUnified elseResult.type
  have unifiedEq : unifiedState.resolve thenResult.type =
      unifiedState.resolve elseResult.type := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq unifySuccess
  have branchEq : finalized.substitution.apply thenResult.type =
      finalized.substitution.apply elseResult.type := by
    calc
      finalized.substitution.apply thenResult.type =
          finalized.substitution.apply
            (unifiedState.resolve thenResult.type) := resolvedThenEq.symm
      _ = finalized.substitution.apply
          (unifiedState.resolve elseResult.type) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply elseResult.type := resolvedElseEq
  have thenType : ExpressionHasType finalized.typedSource active thenResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq]
    exact thenTypeRaw
  have elseType : ExpressionHasType finalized.typedSource active elseResult.id
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) := by
    rw [resolvedThenEq, branchEq]
    exact elseTypeRaw
  have formType : ExpressionFormHasRawType finalized.typedSource active
      ((ExpressionForm.conditional conditionResult.id thenResult.id
        elseResult.id).applySubstitution finalized.substitution)
      (finalized.substitution.apply
        (unifiedState.resolve thenResult.type)) (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.conditional conditionType thenType elseType
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      recorded finalSubstitutionExtends finalRequirementsSubset retained
      (by simpa only [← resources.substitution_eq] using formType)
      (by simpa only [← resources.substitution_eq] using
        thenType.type_admissible)
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

/-- Mapping-index inference exposes only the actual base and key traversals
to recursion.  The two fresh-variable steps and intervening unification are
non-recursive state transitions whose exact source/ledger preservation is
threaded into the two child provenance records. -/
theorem inferExprFuel_success_index_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression baseExpression indexExpression : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value =
      .index baseExpression brackets indexExpression)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (allocatedReady : allocated.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow allocated.inference.next)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentIntegerLiteralsSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState,
      mappingState, indexResult, indexState, baseSuccess, keyFresh, valueFresh,
      mappingSuccess, indexSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_index_facts expressionEq allocationEq success
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [stateEq] using nextBelow
  have baseBelow : baseState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends baseSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have keyBelow : keyState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        baseState baseBelow
    have stateEq : baseState.fresh.2 = keyState := congrArg Prod.snd keyFresh
    simpa [stateEq] using below
  have valueBelow : valueState.NodesBelowNextOccurrence := by
    have below :=
      Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
        keyState keyBelow
    have stateEq : keyState.fresh.2 = valueState :=
      congrArg Prod.snd valueFresh
    simpa [stateEq] using below
  have mappingBelow : mappingState.NodesBelowNextOccurrence :=
    (Detail.unify_occurrenceBoundExtends mappingSuccess
      ).nodesBelowNextOccurrence valueBelow
  have indexBelow : indexState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends indexSuccess
      ).nodesBelowNextOccurrence mappingBelow
  have baseToKey := fresh_eq_typingSourceExtends keyFresh roots
  have keyToValue := fresh_eq_typingSourceExtends valueFresh roots
  have valueToMapping := unify_success_typingSourceExtends mappingSuccess roots
  have mappingToIndex :=
    inferExprFuel_success_typingSourceExtends indexSuccess mappingBelow roots
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have baseOwner : baseState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner baseSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have indexToParent : TypingSourceExtends
      (indexState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans
          (baseOwner.symm.trans
            (baseToKey.owner_eq.symm.trans
              (keyToValue.owner_eq.symm.trans
                (valueToMapping.owner_eq.symm.trans
                  mappingToIndex.owner_eq.symm)))))
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have baseToParent :=
    TypingSourceExtends.trans baseToKey
      (TypingSourceExtends.trans keyToValue
        (TypingSourceExtends.trans valueToMapping
          (TypingSourceExtends.trans mappingToIndex indexToParent)))
  have baseToEvidence :=
    TypingSourceExtends.trans baseToParent parentExtension
  have indexToEvidence :=
    TypingSourceExtends.trans indexToParent parentExtension
  have indexIntegerLiteralsSubset :
      indexState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have mappingIntegerLiteralsSubset :
      mappingState.integerLiterals ⊆ result.2.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset indexSuccess)
      indexIntegerLiteralsSubset
  have valueIntegerLiteralsSubset :
      valueState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    apply mappingIntegerLiteralsSubset
    rw [Detail.unify_integerLiterals mappingSuccess]
    exact member
  have keyIntegerLiteralsSubset :
      keyState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    apply valueIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq valueFresh]
    exact member
  have baseIntegerLiteralsSubset :
      baseState.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    apply keyIntegerLiteralsSubset
    rw [fresh_eq_integerLiterals_eq keyFresh]
    exact member
  have indexRequirementsSubset :
      indexState.requirements ⊆ result.2.requirements :=
    Detail.recordExpressionWithExpected_requirements_subset recorded
  have mappingRequirementsSubset :
      mappingState.requirements ⊆ result.2.requirements :=
    List.Subset.trans
      (Detail.inferExprFuel_requirements_subset indexSuccess)
      indexRequirementsSubset
  have valueRequirementsSubset :
      valueState.requirements ⊆ result.2.requirements := by
    intro requirement member
    apply mappingRequirementsSubset
    rw [Detail.unify_requirements_eq mappingSuccess]
    exact member
  have keyRequirementsSubset :
      keyState.requirements ⊆ result.2.requirements := by
    intro requirement member
    apply valueRequirementsSubset
    rw [fresh_eq_requirements_eq valueFresh]
    exact member
  have baseRequirementsSubset :
      baseState.requirements ⊆ result.2.requirements := by
    intro requirement member
    apply keyRequirementsSubset
    rw [fresh_eq_requirements_eq keyFresh]
    exact member
  let baseChild : ExpressionChildInferenceProvenance (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots) evidenceState roots := {
    fuel
    expression := baseExpression
    expected := none
    initial := allocated
    final := baseState
    inferred := baseResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := baseSuccess
    sourceExtension := baseToEvidence
    integerLiteralsSubset := List.Subset.trans baseIntegerLiteralsSubset
      parentIntegerLiteralsSubset
    requirementsSubset := List.Subset.trans baseRequirementsSubset
      parentRequirementsSubset
  }
  let indexChild : ExpressionChildInferenceProvenance (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots) evidenceState roots := {
    fuel
    expression := indexExpression
    expected := some (mappingState.resolve keyType)
    initial := mappingState
    final := indexState
    inferred := indexResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := mappingBelow
    success := indexSuccess
    sourceExtension := indexToEvidence
    integerLiteralsSubset := List.Subset.trans indexIntegerLiteralsSubset
      parentIntegerLiteralsSubset
    requirementsSubset := List.Subset.trans indexRequirementsSubset
      parentRequirementsSubset
  }
  have baseTypeRaw := resources.expressionHasType_of_childProvenance
    childSound baseChild sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have indexTypeRaw := resources.expressionHasType_of_childProvenance
    childSound indexChild sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have baseProperties := Detail.inferExprFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp at member) baseSuccess
  have keyProperties := Detail.fresh_eq_inferenceProperties
    baseProperties.2.1 keyFresh
  have valueProperties := Detail.fresh_eq_inferenceProperties
    keyProperties.2.1 valueFresh
  have baseAtValue : baseResult.type.VariablesBelow
      valueState.inference.next :=
    baseProperties.2.2.weaken
      (keyProperties.1.trans valueProperties.1).next_le
  have keyAtValue : keyType.VariablesBelow valueState.inference.next :=
    keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingTypeBelow :
      (TypeSystem.Ty.mapping keyType valueType).VariablesBelow
        valueState.inference.next :=
    (TypeSystem.Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyAtValue, valueProperties.2.2⟩
  have unifyProgress := Detail.unify_inferenceProgress
    valueProperties.2.1.solved baseAtValue mappingTypeBelow mappingSuccess
  have mappingReady := Detail.unify_preserves_inferenceReady
    valueProperties.2.1 baseAtValue mappingTypeBelow mappingSuccess
  have keyAtMapping : keyType.VariablesBelow mappingState.inference.next :=
    keyAtValue.weaken unifyProgress.next_le
  have resolvedKeyBelow :
      (mappingState.resolve keyType).VariablesBelow
        mappingState.inference.next :=
    mappingReady.solved.variablesBelow_apply keyAtMapping
  have indexProperties := Detail.inferExprFuel_inferenceProperties
    mappingReady signatureFormation functionsCanonical (by
      intro expectedType member
      simp only [Option.mem_def] at member
      have expectedTypeEq : expectedType = mappingState.resolve keyType :=
        (Option.some.inj member).symm
      rw [expectedTypeEq]
      exact resolvedKeyBelow) indexSuccess
  have allocatedToIndex : allocated.InferenceProgress indexState :=
    baseProperties.1.trans
      (keyProperties.1.trans
        (valueProperties.1.trans
          (unifyProgress.trans indexProperties.1)))
  have expectedAtIndex : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow indexState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken allocatedToIndex.next_le
  have valueAtIndex : valueType.VariablesBelow indexState.inference.next :=
    valueProperties.2.2.weaken
      (unifyProgress.trans indexProperties.1).next_le
  have resolvedValueBelow :
      (indexState.resolve valueType).VariablesBelow
        indexState.inference.next :=
    indexProperties.2.1.solved.variablesBelow_apply valueAtIndex
  have recordedProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      indexProperties.2.1 resolvedValueBelow expectedAtIndex recorded
  have finalIndex : finalized.substitution.SemanticallyExtends
      indexState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordedProperties.1.substitution_extends
  have finalMapping : finalized.substitution.SemanticallyExtends
      mappingState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans finalIndex
      indexProperties.1.substitution_extends
  have unifiedEq : mappingState.resolve baseResult.type =
      mappingState.resolve (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve] using
      Detail.unify_resolve_eq mappingSuccess
  have resolvedBaseEq :
      finalized.substitution.apply
          (mappingState.resolve baseResult.type) =
        finalized.substitution.apply baseResult.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using finalMapping baseResult.type
  have resolvedMappingEq :
      finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) =
        finalized.substitution.apply (.mapping keyType valueType) := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        finalMapping (.mapping keyType valueType)
  have baseEq : finalized.substitution.apply baseResult.type =
      .mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType) := by
    calc
      finalized.substitution.apply baseResult.type =
          finalized.substitution.apply
            (mappingState.resolve baseResult.type) := resolvedBaseEq.symm
      _ = finalized.substitution.apply
          (mappingState.resolve (.mapping keyType valueType)) :=
        congrArg finalized.substitution.apply unifiedEq
      _ = finalized.substitution.apply
          (.mapping keyType valueType) := resolvedMappingEq
      _ = .mapping (finalized.substitution.apply keyType)
          (finalized.substitution.apply valueType) := rfl
  have indexExpectedEq :
      finalized.substitution.apply indexResult.type =
        finalized.substitution.apply
          (mappingState.resolve keyType) :=
    Detail.inferExprFuel_expected_type_apply_eq indexSuccess finalIndex
  have resolvedKeyEq :
      finalized.substitution.apply (mappingState.resolve keyType) =
        finalized.substitution.apply keyType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using finalMapping keyType
  have resolvedValueEq :
      finalized.substitution.apply (indexState.resolve valueType) =
        finalized.substitution.apply valueType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using finalIndex valueType
  have baseType : ExpressionHasType finalized.typedSource active baseResult.id
      (.mapping (finalized.substitution.apply keyType)
        (finalized.substitution.apply valueType)) := by
    rw [← baseEq]
    exact baseTypeRaw
  have indexType : ExpressionHasType finalized.typedSource active indexResult.id
      (finalized.substitution.apply keyType) := by
    rw [← resolvedKeyEq, ← indexExpectedEq]
    exact indexTypeRaw
  have formType : ExpressionFormHasRawType finalized.typedSource active
      ((ExpressionForm.index baseResult.id indexResult.id).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply (indexState.resolve valueType))
      (.ordinary []) := by
    rw [resolvedValueEq]
    simpa [ExpressionForm.applySubstitution] using
      ExpressionFormHasRawType.index baseType indexType
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply (indexState.resolve valueType)) := by
    rw [resolvedValueEq]
    exact TypeAdmissible.mapping_value baseType.type_admissible
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      recorded finalSubstitutionExtends finalRequirementsSubset retained
      (by simpa only [← resources.substitution_eq] using formType)
      (by simpa only [← resources.substitution_eq] using rawAdmissible)
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

/-- The tuple branch consumes the bounded list sequencer without an
unqualified recursive-expression callback.  The successful final recording
supplies the element-state-to-parent node extension and ledger inclusions;
the caller supplies only the parent-to-finalization links. -/
theorem inferExprFuel_success_tuple_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : TypeSystem.Ty}
    {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat}
    {expression : Syntax.Expr}
    {elements : Syntax.DelimitedList Syntax.Expr}
    {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .tuple elements)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (parentIntegerLiteralsSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (activeBinders : TypeParameterBindersWellFormed active)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  obtain ⟨inferredElements, elementsState, elementsSuccess, recorded⟩ :=
    Detail.inferExprFuel_success_tuple_facts expressionEq allocationEq success
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have nextBelow :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [stateEq] using nextBelow
  have allocatedOwner : allocated.owner = initial.owner := by
    have stateEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← stateEq]
    rfl
  have elementsOwner : elementsState.owner = allocated.owner :=
    inferExprsFuel_success_owner_eq elementsSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner success
  have elementsToParent : TypingSourceExtends
      (elementsState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans elementsOwner.symm)
    · exact recordExpressionWithExpected_success_nodesPrefix recorded
  have elementsToEvidence : TypingSourceExtends
      (elementsState.toTypedSource roots)
      (evidenceState.toTypedSource roots) :=
    TypingSourceExtends.trans elementsToParent parentExtension
  have elementsIntegerLiteralsSubset :
      elementsState.integerLiterals ⊆ evidenceState.integerLiterals := by
    intro origin member
    apply parentIntegerLiteralsSubset
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recorded]
    exact member
  have elementsRequirementsSubset :
      elementsState.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recorded)
      parentRequirementsSubset
  have elementBases : ArgumentTypingBasesValid
      (elementsState.toTypedSource roots) finalized.typedSource active
      finalized.substitution inferredElements :=
    inferExprsFuel_success_argumentTypingBasesValid_under_ambient_bounded
      (roots := roots) (Nat.lt_succ_self fuel) allocatedBelow
      elementsToEvidence elementsIntegerLiteralsSubset
      elementsRequirementsSubset childSound elementsSuccess
  have elementsType : ExpressionsHaveTypes finalized.typedSource active
      (inferredElements.map (·.id))
      (inferredElements.map fun element =>
        finalized.substitution.apply element.type) :=
    resources.expressionsHaveTypes_of_argumentTypingBases_prefix elementBases
      elementsToEvidence sourceBinders signaturesEq parametersEq ownerEq
      residual contextValid
  have formType : ExpressionFormHasRawType finalized.typedSource active
      ((ExpressionForm.tuple (inferredElements.map (·.id))).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply
        (TypeSystem.Ty.productMany (inferredElements.map (·.type))))
      (.ordinary []) := by
    simpa [ExpressionForm.applySubstitution,
      FlexibleSubstitution.apply_productMany, List.map_map,
      Function.comp_def] using ExpressionFormHasRawType.tuple elementsType
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply
        (TypeSystem.Ty.productMany (inferredElements.map (·.type)))) := by
    simpa [FlexibleSubstitution.apply_productMany, List.map_map,
      Function.comp_def] using
        elementsType.product_type_admissible activeBinders
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalRequirementsSubset :
      result.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact parentRequirementsSubset member
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      recorded finalSubstitutionExtends finalRequirementsSubset retained
      (by simpa only [← resources.substitution_eq] using formType)
      (by simpa only [← resources.substitution_eq] using rawAdmissible)
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      traitName resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono covered)

end Solcore.SourceSemantics.SourceInferenceSoundness
