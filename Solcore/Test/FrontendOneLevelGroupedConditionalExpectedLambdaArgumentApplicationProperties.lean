import Solcore.Frontend.OneLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Machine

/-! Independent symbolic consumer for one whole-group conditional adapter. -/
set_option autoImplicit false

namespace Tests.ADR0326OneLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"GroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 326
private def foreignOwner := declaration 9326
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩,
  ⟨"apply", localId owner 3, .unit⟩, ⟨"flag", localId foreignOwner 701, .bool⟩,
  ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "adr0326-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr :=
  ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block :=
  ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2),
    [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr :=
  ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr :=
  call n callee (groups [n + 5] (conditional n condition yes no))
private def selected (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr :=
  candidate n (ref (n + 1) "apply") (ref (n + 2) "flag") yes no
private def ungrouped (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr :=
  call n (ref (n + 1) "apply") (conditional n (ref (n + 2) "flag") yes no)
private def twoGroups (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr :=
  call n (ref (n + 1) "apply") (groups [n + 5, n + 6]
    (conditional n (ref (n + 2) "flag") yes no))
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def conditionalCore (yes no : Core.Expr) : Core.Expr :=
  .apply (.var 0) (.ifE (.var 3) yes no)

private theorem applyE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "flag") (.var 3) .bool := .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "ordinary") (.var 4) functionType := .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem wrongE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "wrong") (.var 5) .word := .pure (.identifier (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "opaque" ≠ "wrong"; decide) (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "flag" ≠ "wrong"; decide) (.tail (by change "ordinary" ≠ "wrong"; decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
private theorem lambdaE (n : Nat) (name : String) : ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs (lambda n name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))
private theorem applyC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context
    (ref n "apply") = some (.var 0, .function functionType .word) :=
  elaborateRecursiveLocalComputation?_iff.mpr (applyE n)
private theorem flagC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context
    (ref n "flag") = some (.var 3, .bool) :=
  elaborateRecursiveLocalComputation?_iff.mpr (flagE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context
    (ref n "wrong") = some (.var 5, .word) :=
  elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation?
    inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
    resolveLocalExpression?, absent]

private def cLO := selected 0 (lambda 10 "x") (ref 30 "ordinary")
private def cOL := selected 40 (ref 70 "ordinary") (lambda 80 "y")
private def cLL := selected 90 (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr)
    (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc)
    (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc)
    (boundary : (isImmediateExpectedComputationLambda yes ||
      isImmediateExpectedComputationLambda no) = true) :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs (selected n yes no) (conditionalCore yc nc) .word :=
  .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x"))
  (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70))
  (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x"))
  (.expected rfl (lambdaE 120 "y")) rfl
private theorem noOldGroup (n : Nat) (yes no : Syntax.Expr) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr
  intro old
  obtain ⟨_, _, _, _, _, spine⟩ :=
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child
private def Contract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧
  isConditionalExpectedLambdaArgumentApplication s = false ∧
  isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧
  OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs s c .word ∧
  elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
    types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word
private theorem contract {s c} (e :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs s c .word)
    (oldGroup : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) :
    Contract s c := by
  refine ⟨e.classified, ?_, oldGroup, e,
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e,
    e.core_hasType⟩
  cases e
  rfl
private theorem provenancesAreComplete : True := by
  have _ := eLO.provenance
  have _ := eOL.provenance
  have _ := eLL.provenance
  trivial

/-- All three branch partitions independently retain exact static semantics. -/
theorem all_three_grouped_conditional_partitions_have_exact_semantics :
    Contract cLO coreLO ∧ Contract cOL coreOL ∧ Contract cLL coreLL :=
  ⟨contract eLO (noOldGroup 0 _ _), contract eOL (noOldGroup 40 _ _),
    contract eLL (noOldGroup 90 _ _)⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) []
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31,
    .bool choice, ordinaryValue, .word seven]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def exactFuel (choice : Bool) (core : Core.Expr) : Prop :=
  (match Core.runStateful 13 (Core.State.initial core (environment choice) store) with
   | .outOfFuel _ => True | _ => False) ∧
  Core.runStateful 14 (Core.State.initial core (environment choice) store) =
    .done (.word seven) store
private theorem fuels : ∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core := by
  intro choice core member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cases choice <;>
    exact ⟨True.intro, rfl⟩

/-- Both choices require exactly fuel 14 and preserve the literal nonempty store. -/
theorem both_choices_have_exact_fuel_and_preserve_store :
    ∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core := fuels

private def badHeader (n : Nat) : Syntax.Expr :=
  ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), []⟩ none (body n "x")⟩
private def badBody (n : Nat) : Syntax.Expr :=
  ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2),
    [⟨span (n + 2), .inferred ⟨span (n + 2), "x"⟩⟩]⟩ none
    ⟨span (n + 3), [⟨span (n + 4), .returnStmt none⟩]⟩⟩
private theorem badHeaderNone (n : Nat) : elaborateConditionalExpectedLambdaBranch?
    types owner inputs (badHeader n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch? elaborateExpectedComputationLambda?
    declareExpectedUnaryLambdaHeader? badHeader
  rfl
private theorem badBodyNone (n : Nat) : elaborateConditionalExpectedLambdaBranch?
    types owner inputs (badBody n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch? elaborateExpectedComputationLambda?
    declareExpectedUnaryLambdaHeader? badBody functionType types Core.Ty.isWellFormed
    elaborateComputationReturnTree?
  rfl
private theorem wrongNone (n : Nat) : elaborateConditionalExpectedLambdaBranch?
    types owner inputs (ref n "wrong") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?
  rw [show isImmediateExpectedComputationLambda (ref n "wrong") = false by rfl]
  simp [wrongC, functionType]
private theorem groupedLambdaNone (n m : Nat) : elaborateConditionalExpectedLambdaBranch?
    types owner inputs (groups [n] (lambda m "y")) functionType = none := by
  have rejected : elaborateRecursiveLocalComputation? inputs.names inputs.context
      (groups [n] (lambda m "y")) = none := by
    simp [groups, lambda, body, ref, elaborateRecursiveLocalComputation?,
      elaborateLocalExpression?, resolveLocalExpression?]
  unfold elaborateConditionalExpectedLambdaBranch?
  rw [show isImmediateExpectedComputationLambda (groups [n] (lambda m "y")) = false by rfl]
  simp [rejected]
private def failures := [
  candidate 200 (ref 201 "apply") (ref 202 "wrong") (lambda 210 "x") (ref 220 "ordinary"),
  selected 230 (badHeader 240) (ref 250 "ordinary"),
  selected 260 (badBody 270) (ref 280 "ordinary"),
  selected 290 (lambda 300 "x") (ref 310 "wrong"),
  candidate 320 (ref 321 "flag") (ref 322 "flag") (lambda 330 "x") (ref 340 "ordinary"),
  candidate 350 (ref 351 "missing") (ref 352 "flag") (lambda 360 "x") (ref 370 "ordinary"),
  selected 380 (lambda 390 "x") (groups [400] (lambda 410 "y"))]
private theorem failuresFinal : ∀ source ∈ failures,
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs source = none := by
  intro source member
  simp only [failures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC,
      badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC,
      badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC,
      wrongNone]⟩
  · exact ⟨rfl, by simp [candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, groups, conditional, call,
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩
    cases e with
    | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee
      rw [applyC] at c
      cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no
      rw [groupedLambdaNone] at rejected
      cases rejected

private def frozenUngrouped := ungrouped 500 (lambda 510 "x") (ref 520 "ordinary")
private def frozenTwo := twoGroups 530 (lambda 540 "x") (ref 550 "ordinary")
private def frozenOrdinary := selected 560 (ref 570 "ordinary") (ref 580 "ordinary")
private def returnArgument : Syntax.Expr := ⟨span 700, .lambda (span 701) ⟨span 702, [⟨span 702, .inferred ⟨span 702, "x"⟩⟩]⟩ none ⟨span 703, [⟨span 704, .returnStmt (some (lambda 710 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 720, .lambda (span 721) ⟨span 722, [⟨span 722, .inferred ⟨span 722, "x"⟩⟩]⟩ none ⟨span 723, [⟨span 724, .letDecl ⟨span 725, "y"⟩ none (some (lambda 730 "z"))⟩, ⟨span 726, .returnStmt (some (ref 727 "x"))⟩]⟩⟩
private def neighboringControls := [⟨span 600, .call (ref 601 "apply") ⟨span 602, []⟩⟩, ⟨span 610, .call (ref 611 "apply") ⟨span 612, [lambda 613 "x", ref 614 "ordinary"]⟩⟩, conditional 620 (ref 622 "flag") (lambda 630 "x") (ref 640 "ordinary"), call 650 (ref 651 "apply") ⟨span 652, .tuple ⟨span 653, [lambda 654 "x", ref 655 "ordinary"]⟩⟩, call 660 (ref 661 "ordinary") (call 662 (ref 663 "apply") (lambda 664 "x")), call 680 (ref 681 "apply") returnArgument, call 690 (ref 691 "apply") letArgument]
private theorem neighboringFrozen : ∀ source ∈ neighboringControls, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs source = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source := by
  intro source member; simp only [neighboringControls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, rfl, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing rfl ?_⟩
  all_goals first | rfl | (apply Bool.eq_false_iff.mpr; intro selected; obtain ⟨_,_,_,_,_,spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected; cases spine)
private theorem oldUngrouped : elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    types owner inputs frozenUngrouped = some (coreLO, .word) := by
  apply elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr
  exact .conditional rfl (.application rfl (applyE 501) (flagE 502)
    (.expected rfl (lambdaE 510 "x")) (.ordinary rfl (ordinaryE 520)))
private theorem frozenTwoExact : elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    types owner inputs frozenTwo = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs frozenTwo := by
  apply elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing rfl
  apply Bool.eq_false_iff.mpr
  intro old
  obtain ⟨_, _, _, _, _, spine⟩ :=
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild
private theorem frozenOrdinaryOld : elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
    types owner inputs frozenOrdinary = some (conditionalCore (.var 4) (.var 4), .word) := by
  apply elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr
  exact .existing rfl (noOldGroup 560 _ _) (.existing rfl (.existing rfl (.ordinary rfl
    (.application (applyE 561) (.group (.conditional (flagE 562)
      (ordinaryE 570) (ordinaryE 580)))))))

/-- Every recognized failure is final and every noncandidate retains ADR0325 exactly. -/
theorem recognized_failures_and_frozen_boundaries_are_exact :
    (∀ source ∈ failures, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs source = none) ∧
    (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication frozenUngrouped = false ∧
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs frozenUngrouped = none ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs frozenUngrouped = some (coreLO, .word)) ∧
    (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication frozenTwo = false ∧
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs frozenTwo = none ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs frozenTwo = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs frozenTwo) ∧
    (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication frozenOrdinary = false ∧
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs frozenOrdinary = none ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs frozenOrdinary = some (conditionalCore (.var 4) (.var 4), .word)) ∧
    (∀ source ∈ neighboringControls, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs source = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source) := by
  exact ⟨failuresFinal, ⟨rfl, rfl, oldUngrouped⟩, ⟨rfl, rfl, frozenTwoExact⟩,
    ⟨rfl, rfl, frozenOrdinaryOld⟩, neighboringFrozen⟩

end Tests.ADR0326OneLevelGroupedConditionalSymbolicConsumerIndependent
