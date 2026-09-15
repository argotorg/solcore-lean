import Solcore.Frontend.TwoLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithOneLevelGroupedConditionalExpectedLambda
import Solcore.Core.Machine

/-! Independent symbolic consumer for the exact two-whole-group conditional adapter. -/
set_option autoImplicit false

namespace Tests.ADR0328TwoLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TwoGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 328
private def foreignOwner := declaration 9328
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29
private def wrongId := localId foreignOwner 702
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", applyId, .function functionType .word⟩, ⟨"opaque", opaqueId, .cell (.function .word .unit)⟩, ⟨"apply", duplicateId, .unit⟩, ⟨"flag", flagId, .bool⟩, ⟨"ordinary", ordinaryId, functionType⟩, ⟨"wrong", wrongId, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "adr0328-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6] callee condition yes no
private def selected (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr := candidate n (ref (n + 1) "apply") (ref (n + 2) "flag") yes no
private def selectedAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : Syntax.Expr := atGroups n ns (ref (n + 1) "apply") (ref (n + 2) "flag") yes no
private def lambdaApplication (n : Nat) (ns : List Nat) : Syntax.Expr := call n (ref (n + 1) "apply") (groups ns (lambda (n + 20) "x"))
private def ordinaryApplication (n : Nat) : Syntax.Expr := call n (ref (n + 1) "apply") (ref (n + 20) "ordinary")
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def conditionalCore (yes no : Core.Expr) : Core.Expr := .apply (.var 0) (.ifE (.var 3) yes no)

private theorem applyE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "flag") (.var 3) .bool := .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "ordinary") (.var 4) functionType := .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem wrongE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "wrong") (.var 5) .word := .pure (.identifier (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "opaque" ≠ "wrong"; decide) (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "flag" ≠ "wrong"; decide) (.tail (by change "ordinary" ≠ "wrong"; decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
private theorem lambdaE (n : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambda n name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem applyC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") = some (.var 0, .function functionType .word) := elaborateRecursiveLocalComputation?_iff.mpr (applyE n)
private theorem flagC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "flag") = some (.var 3, .bool) := elaborateRecursiveLocalComputation?_iff.mpr (flagE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent]

private def cLO := selected 0 (lambda 10 "x") (ref 30 "ordinary")
private def cOL := selected 40 (ref 70 "ordinary") (lambda 80 "y")
private def cLL := selected 90 (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def Provenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan innerGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨innerGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def Contract (s : Syntax.Expr) (c : Core.Expr) : Prop := isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ Provenance s c
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild
private theorem contract {s c} (e : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) : Contract s c :=
  ⟨e.classified, by cases e; rfl, by cases e; rfl, finite, e, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance⟩

/-! All three branch partitions retain the exact relation, checker, Core, type and provenance. -/
theorem all_three_two_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ Contract cLO coreLO ∧ Contract cOL coreOL ∧ Contract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact contract eLO (noFinite 0 _ _)
  · exact contract eOL (noFinite 40 _ _)
  · exact contract eLL (noFinite 90 _ _)

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) []
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def exactFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 13 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 14 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private theorem fuels : ∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core := by
  intro choice core member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩

/-! Both Boolean choices require fuel 14 and preserve the literal nonempty store. -/
theorem both_choices_have_exact_fuel_and_preserve_store :
    ∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core := fuels

private def badHeader (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), []⟩ none (body n "x")⟩
private def badBody (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), "x"⟩⟩]⟩ none ⟨span (n + 3), [⟨span (n + 4), .returnStmt none⟩]⟩⟩
private theorem badHeaderNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badHeader n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch? elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
private theorem badBodyNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badBody n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch? elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBody functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl
private theorem wrongNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (ref n "wrong") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (ref n "wrong") = false by rfl]; simp [wrongC, functionType]
private theorem missingBranchNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (ref n "missing") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (ref n "missing") = false by rfl]; simp [missingC]
private theorem groupedLambdaNone (n m : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (groups [n] (lambda m "y")) functionType = none := by
  have rejected : elaborateRecursiveLocalComputation? inputs.names inputs.context (groups [n] (lambda m "y")) = none := by simp [groups, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (groups [n] (lambda m "y")) = false by rfl]; simp [rejected]
private def nestedLambdaCall (n : Nat) : Syntax.Expr := call n (ref (n + 1) "ordinary") (lambda (n + 10) "z")
private theorem nestedLambdaCallNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (nestedLambdaCall n) functionType = none := by
  have argument : elaborateRecursiveLocalComputation? inputs.names inputs.context (lambda (n + 10) "z") = none := by simp [lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
  have nested : elaborateRecursiveLocalComputation? inputs.names inputs.context (nestedLambdaCall n) = none := by simp [nestedLambdaCall, call, elaborateRecursiveLocalComputation?, argument]
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (nestedLambdaCall n) = false by rfl]; simp [nested]
private def failures := [candidate 200 (ref 201 "apply") (ref 202 "wrong") (lambda 210 "x") (ref 220 "ordinary"), candidate 230 (ref 231 "apply") (ref 232 "missing") (lambda 240 "x") (ref 250 "ordinary"), selected 260 (badHeader 270) (ref 280 "ordinary"), selected 290 (badBody 300) (ref 310 "ordinary"), selected 320 (lambda 330 "x") (ref 340 "wrong"), selected 350 (lambda 360 "x") (ref 370 "missing"), candidate 380 (ref 381 "flag") (ref 382 "flag") (lambda 390 "x") (ref 400 "ordinary"), candidate 410 (ref 411 "missing") (ref 412 "flag") (lambda 420 "x") (ref 430 "ordinary"), selected 440 (lambda 450 "x") (groups [460] (lambda 470 "y")), selected 480 (lambda 490 "x") (nestedLambdaCall 500)]
private theorem failuresFinal : ∀ source ∈ failures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [failures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩

private def PreservesADR0327 (source : Syntax.Expr) : Prop := isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source
private theorem preservesADR0327 {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (rejected : elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none) : PreservesADR0327 source := ⟨boundary, rejected, by simp [boundary]⟩
private def boundaryNeighbors := [selectedAt 600 [605] (lambda 610 "x") (ref 620 "ordinary"), selectedAt 630 [635, 636, 637] (lambda 640 "x") (ref 650 "ordinary"), selected 660 (ref 670 "ordinary") (ref 680 "ordinary"), selected 690 (groups [700] (lambda 710 "x")) (ref 720 "ordinary"), selected 730 (nestedLambdaCall 740) (ref 750 "ordinary")]
private theorem boundaryNeighborsPreserved : ∀ source ∈ boundaryNeighbors, PreservesADR0327 source := by
  intro source member; simp only [boundaryNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact preservesADR0327 rfl rfl
private def predecessorRoutes := [selectedAt 760 [] (lambda 770 "x") (ref 780 "ordinary"), lambdaApplication 790 [], lambdaApplication 820 [823], lambdaApplication 850 [853, 854], lambdaApplication 880 [883, 884, 885], ordinaryApplication 910]
private theorem predecessorRoutesPreserved : ∀ source ∈ predecessorRoutes, PreservesADR0327 source := by
  intro source member; simp only [predecessorRoutes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact preservesADR0327 rfl rfl
private theorem failuresStayFinal : ∀ source ∈ failures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source) = none := by
  intro source member
  have h := failuresFinal source member
  exact ⟨h.1, h.2, by simp [h.1, h.2]⟩

/-! Selected failures remain final; every false shape retains the complete ADR-0327 Option. -/
theorem recognized_failures_and_complete_adr0327_options_are_exact :
    (∀ source ∈ failures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source) = none) ∧
    (∀ source ∈ boundaryNeighbors, PreservesADR0327 source) ∧
    (∀ source ∈ predecessorRoutes, PreservesADR0327 source) ∧
    (∀ t o i s, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨failuresStayFinal, boundaryNeighborsPreserved, predecessorRoutesPreserved, by intro _ _ _ _ h; simp [h]⟩

end Tests.ADR0328TwoLevelGroupedConditionalSymbolicConsumerIndependent
