import Solcore.Frontend.LocalApplicationWithTwoLevelGroupedConditionalExpectedLambda
import Solcore.Core.Machine
import Solcore.Core.Correspondence

/-! Independent symbolic consumer for the ADR-0328-first ADR-0327 wrapper. -/
set_option autoImplicit false

namespace Tests.ADR0329TwoLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TwoGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 329
private def foreignOwner := declaration 9329
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
private def file : Syntax.SourceId := ⟨.main, "adr0329-symbolic.sol"⟩
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
private def expectedCore : Core.Expr := .apply (.var 0) lambdaCore
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)

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
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan innerGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨innerGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  ((isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild
private theorem newContract {s c} (e : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) : NewContract s c := by
  let wrapped : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .twoLevelGroupedConditional e.classified e
  refine ⟨e.classified, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional e.classified, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, wrapped.core_hasType, ?_⟩
  exact ⟨wrapped.provenance, e.provenance⟩

/-! The three selected source partitions retain both complete relations and nested provenance. -/
theorem all_three_two_level_grouped_conditional_routes_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _)
  · exact newContract eOL (noFinite 40 _ _)
  · exact newContract eLL (noFinite 90 _ _)

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) []
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def exactConditionalFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 13 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 14 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private def exactLambdaFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 10 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 11 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private def allOrdinaryCore := conditionalCore (.var 4) (.var 4)
private theorem conditionalFuels : ∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core := by
  intro choice core member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩
private theorem lambdaFuels : ∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core := by
  intro choice core member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩
private theorem finish {choice : Bool} {argument : Core.Expr} {captured : Core.Environment}
    (runs : Core.Evaluates (environment choice) store argument (.closure .word .word (.var 0) captured) store) :
    Core.Evaluates (environment choice) store (.apply (.var 0) argument) (.word seven) store :=
  .apply (.var rfl) runs (.apply (.var rfl) .word (.var rfl))
private theorem conditionalRuns (choice : Bool) : Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store := by
  cases choice
  · exact ⟨finish (.ifFalse (.var rfl) (.var rfl)), finish (.ifFalse (.var rfl) .lambda), finish (.ifFalse (.var rfl) .lambda), finish (.ifFalse (.var rfl) (.var rfl))⟩
  · exact ⟨finish (.ifTrue (.var rfl) .lambda), finish (.ifTrue (.var rfl) (.var rfl)), finish (.ifTrue (.var rfl) .lambda), finish (.ifTrue (.var rfl) (.var rfl))⟩
private theorem lambdaRuns (choice : Bool) : Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store := ⟨finish .lambda, finish (.var rfl)⟩
private theorem conditionalRunnerSound (choice : Bool) (core : Core.Expr) (member : core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore]) : Core.Evaluates (environment choice) store core (.word seven) store :=
  Core.runStateful_evaluation_sound (conditionalFuels choice core member).2
private theorem lambdaRunnerSound (choice : Bool) (core : Core.Expr) (member : core ∈ [expectedCore, ordinaryCore]) : Core.Evaluates (environment choice) store core (.word seven) store :=
  Core.runStateful_evaluation_sound (lambdaFuels choice core member).2
private theorem conditionalDeterministic (choice : Bool) (core : Core.Expr) (member : core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore]) (value : Core.Value) (finalStore : Core.Store) (other : Core.Evaluates (environment choice) store core value finalStore) : value = .word seven ∧ finalStore = store :=
  Core.evaluation_deterministic other (conditionalRunnerSound choice core member)
private theorem lambdaDeterministic (choice : Bool) (core : Core.Expr) (member : core ∈ [expectedCore, ordinaryCore]) (value : Core.Value) (finalStore : Core.Store) (other : Core.Evaluates (environment choice) store core value finalStore) : value = .word seven ∧ finalStore = store :=
  Core.evaluation_deterministic other (lambdaRunnerSound choice core member)

private def badHeader (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), []⟩ none (body n "x")⟩
private def badBody (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), "x"⟩⟩]⟩ none ⟨span (n + 3), [⟨span (n + 4), .returnStmt none⟩]⟩⟩
private theorem badHeaderNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badHeader n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch? elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
private theorem badExpectedNone (n : Nat) : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs (badHeader n) functionType = none := by
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
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
private def selectedFailures := [candidate 200 (ref 201 "apply") (ref 202 "wrong") (lambda 210 "x") (ref 220 "ordinary"), candidate 230 (ref 231 "apply") (ref 232 "missing") (lambda 240 "x") (ref 250 "ordinary"), selected 260 (badHeader 270) (ref 280 "ordinary"), selected 290 (badBody 300) (ref 310 "ordinary"), selected 320 (lambda 330 "x") (ref 340 "wrong"), selected 350 (lambda 360 "x") (ref 370 "missing"), candidate 380 (ref 381 "flag") (ref 382 "flag") (lambda 390 "x") (ref 400 "ordinary"), candidate 410 (ref 411 "missing") (ref 412 "flag") (lambda 420 "x") (ref 430 "ordinary"), selected 440 (lambda 450 "x") (groups [460] (lambda 470 "y")), selected 480 (lambda 490 "x") (nestedLambdaCall 500)]
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional h.1, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional h.1).trans h.2⟩

private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def lambdaControls := [lambdaApplication 620 [], lambdaApplication 650 [653], lambdaApplication 680 [683, 684], lambdaApplication 710 [713, 714, 715]]
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem spineFrom {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) (ns : List Nat) : DirectLambdaGroupSpine (groups ns terminal) (ns.map span) terminal := by
  induction ns with | nil => exact base | cons _ _ ih => exact .group ih
private theorem spineUnique {s a b : Syntax.Expr} {xs ys : List Syntax.SourceSpan} (x : DirectLambdaGroupSpine s xs a) (y : DirectLambdaGroupSpine s ys b) : xs = ys ∧ a = b := by
  induction x generalizing ys b with | lambda => cases y; exact ⟨rfl, rfl⟩ | group _ ih => cases y with | group z => obtain ⟨rfl, rfl⟩ := ih z; exact ⟨rfl, rfl⟩
private theorem shallowFalse (n : Nat) (ns : List Nat) (small : ns.length < 3) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (lambdaApplication n ns) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, rest, _, other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  have lengths := congrArg List.length (spineUnique (spineFrom .lambda ns) other).1
  simp at lengths; omega
private theorem lambda0E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 620 []) expectedCore .word := .existing rfl (shallowFalse 620 [] (by decide)) (.existing rfl (.existing rfl (.expected rfl (.application (applyE 621) (lambdaE 640 "x")))))
private theorem lambda1E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 650 [653]) expectedCore .word := .existing rfl (shallowFalse 650 [653] (by decide)) (.existing rfl (.grouped rfl (.application (applyE 651) (lambdaE 670 "x"))))
private theorem lambda2E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 680 [683, 684]) expectedCore .word := .existing rfl (shallowFalse 680 [683, 684] (by decide)) (.twoLevel rfl (.application (applyE 681) (lambdaE 700 "x")))
private theorem lambda3E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 710 [713, 714, 715]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 710 [713, 714, 715]) expectedCore .word := .application (spineFrom .lambda [713, 714, 715]) (applyE 711) (lambdaE 730 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem existingCheck {source core} (boundary : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs source core .word) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing boundary]
  exact elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by
  intro ns; induction ns with
  | nil => intro _ _ spine; cases spine
  | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem conditionalOldNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  calc
    _ = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one
    _ = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite
    _ = elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two
    _ = elaborateLocalApplicationWithExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped
    _ = none := by simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private def threeGroupConditional := selectedAt 760 [765, 766, 767] (lambda 770 "x") (ref 790 "ordinary")
private def allOrdinarySource := selectedAt 800 [805, 806] (ref 810 "ordinary") (ref 820 "ordinary")
private def groupedOnlySource := selectedAt 830 [835, 836] (groups [840] (lambda 850 "x")) (ref 870 "ordinary")
private def nestedOnlySource := selectedAt 880 [885, 886] (nestedLambdaCall 890) (ref 910 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 800 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 801) (.group (.group (.conditional (flagE 802) (ordinaryE 810) (ordinaryE 820))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(oneGroupControl, some (coreLO, .word)), (immediateControl, some (coreLO, .word)), (threeGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : CompleteOption (source, result) := by
  have branch := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, exact, branch, branch.trans exact, ?_⟩
  intro core type observed
  have child := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed)
  let wrapped : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child
  exact ⟨child, wrapped, wrapped.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr oneGroupE)
  · exact completeOption (existingCheck rfl immediateE)
  · exact completeOption (by simpa only [threeGroupConditional] using conditionalOldNone 760 [765, 766, 767] (lambda 770 "x") (ref 790 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (existingCheck rfl allOrdinaryE)
  · exact completeOption (by simpa only [groupedOnlySource] using conditionalOldNone 830 [835, 836] (groups [840] (lambda 850 "x")) (ref 870 "ordinary") rfl rfl (noFiniteAt 830 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (by simpa only [nestedOnlySource] using conditionalOldNone 880 [885, 886] (nestedLambdaCall 890) (ref 910 "ordinary") rfl rfl (noFiniteAt 880 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (existingCheck rfl lambda0E)
  · exact completeOption (existingCheck rfl lambda1E)
  · exact completeOption (existingCheck rfl lambda2E)
  · exact completeOption (existingCheck rfl lambda3E)
  · exact completeOption (existingCheck rfl ordinaryApplicationE)
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (oneGroupControl, some (coreLO, .word)), (immediateControl, some (coreLO, .word)), (allOrdinarySource, some (allOrdinaryCore, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word))]
private theorem neighborCheck {item} (member : item ∈ completeNeighbors) : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := (completeOptionsExact item member).2.2.2.1
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr (.twoLevelGroupedConditional eLO.classified eLO)
  · exact elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr (.twoLevelGroupedConditional eOL.classified eOL)
  · exact elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr (.twoLevelGroupedConditional eLL.classified eLL)
  all_goals exact neighborCheck (by simp [completeNeighbors])

/-! Child Cores stay literal; manual, runner-sound and deterministic execution agree. -/
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousOneConditionalNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary")) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional (by rfl)]; simp [elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousImmediateConditionalNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary")) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_conditional (by rfl)]; simp [elaborateConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem shallowTerminalFalse (n callee : Nat) {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) (ns : List Nat) (small : ns.length < 3) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (call n (ref callee "apply") (groups ns terminal)) = false := by apply Bool.eq_false_iff.mpr; intro h; obtain ⟨_, _, _, rest, _, other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h; have lengths := congrArg List.length (spineUnique (spineFrom base ns) other).1; simp at lengths; omega
private theorem previousThreeGroupLambdaNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170))) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_threeOrMoreGrouped (source := call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170))) (by rfl) (isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mpr ⟨span 1163, span 1164, span 1165, [], badHeader 1170, spineFrom .lambda [1163, 1164, 1165]⟩)]; apply elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr; rintro ⟨_, _, e⟩; cases e with | application spine callee argument => have same := (spineUnique (spineFrom (terminal := badHeader 1170) .lambda [1163, 1164, 1165]) spine).2; cases same; have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c; have a := (elaborateExpectedComputationLambda?_iff (@elaborateRecursiveLocalComputation?_iff)).mpr argument; rw [badExpectedNone] at a; cases a
private theorem previousTwoGroupLambdaNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190))) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing (by rfl) (shallowTerminalFalse 1180 1181 (terminal := badHeader 1190) .lambda [1183, 1184] (by decide)), elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel (by rfl)]; simp [elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, groups, call, applyC, badExpectedNone]
private theorem previousOneGroupLambdaNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210))) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing (by rfl) (shallowTerminalFalse 1200 1201 (terminal := badHeader 1210) .lambda [1203] (by decide)), elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped (by rfl)]; simp [elaborateGroupedExpectedLambdaArgumentApplication?, groups, call, applyC, badExpectedNone]
private theorem previousDirectLambdaNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1220 (ref 1221 "apply") (badHeader 1230)) = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing (by rfl) (by simpa [groups] using shallowTerminalFalse 1220 1221 (terminal := badHeader 1230) .lambda [] (by decide)), elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing (by rfl), elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing (by rfl)]; unfold elaborateLocalApplicationWithExpectedLambda?; rw [show isDirectExpectedLambdaArgumentApplication (call 1220 (ref 1221 "apply") (badHeader 1230)) = true by rfl]; simp [elaborateExpectedLambdaArgumentApplication?, call, applyC, badExpectedNone]
private theorem previousExistingNone {source : Syntax.Expr} (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (conditional : isConditionalExpectedLambdaArgumentApplication source = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication source = false) (final : elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing conditional finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]; exact final
private theorem expectedAbsent {source : Syntax.Expr} (absent : ¬ ∃ core, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs source core functionType) : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs source functionType = none := (elaborateExpectedComputationLambda?_eq_none_iff (@elaborateRecursiveLocalComputation?_iff)).mpr absent
private theorem returnExpectedNone : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs returnArgument functionType = none := expectedAbsent (by rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with | expression e => cases e with | pure r _ _ => cases r)
private theorem letExpectedNone : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs letArgument functionType = none := expectedAbsent (by rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with | inferred e _ => cases e with | pure r _ _ => cases r)
private theorem tuplePreviousNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩) = none := by apply previousExistingNone rfl rfl (by apply Bool.eq_false_iff.mpr; intro h; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h; cases spine) rfl rfl; unfold elaborateLocalApplicationWithExpectedLambda?; rw [show isDirectExpectedLambdaArgumentApplication (call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩) = false by rfl]; simp [call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem nestedPreviousNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x"))) = none := by apply previousExistingNone rfl rfl (by apply Bool.eq_false_iff.mpr; intro h; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h; cases spine) rfl rfl; unfold elaborateLocalApplicationWithExpectedLambda?; rw [show isDirectExpectedLambdaArgumentApplication (call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x"))) = false by rfl]; simp [call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem returnPreviousNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1280 (ref 1281 "apply") returnArgument) = none := by apply previousExistingNone rfl rfl (by simpa [groups] using shallowTerminalFalse 1280 1281 (terminal := returnArgument) .lambda [] (by decide)) rfl rfl; unfold elaborateLocalApplicationWithExpectedLambda?; rw [show isDirectExpectedLambdaArgumentApplication (call 1280 (ref 1281 "apply") returnArgument) = true by rfl]; simp [elaborateExpectedLambdaArgumentApplication?, call, applyC, returnExpectedNone]
private theorem letPreviousNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (call 1290 (ref 1291 "apply") letArgument) = none := by apply previousExistingNone rfl rfl (by simpa [groups] using shallowTerminalFalse 1290 1291 (terminal := letArgument) .lambda [] (by decide)) rfl rfl; unfold elaborateLocalApplicationWithExpectedLambda?; rw [show isDirectExpectedLambdaArgumentApplication (call 1290 (ref 1291 "apply") letArgument) = true by rfl]; simp [elaborateExpectedLambdaArgumentApplication?, call, applyC, letExpectedNone]
private def inheritedAndBoundaryFailures := [selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousOneConditionalNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousOneConditionalNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousImmediateConditionalNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousImmediateConditionalNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousThreeGroupLambdaNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousThreeGroupLambdaNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousTwoGroupLambdaNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousTwoGroupLambdaNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousOneGroupLambdaNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousOneGroupLambdaNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, previousDirectLambdaNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans previousDirectLambdaNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, tuplePreviousNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans tuplePreviousNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, nestedPreviousNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans nestedPreviousNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, returnPreviousNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans returnPreviousNone⟩ | exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl, letPreviousNone, (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing rfl).trans letPreviousNone⟩

/-! Selected failures are final; every false neighbor retains its literal ADR-0327 Option. -/
theorem selected_failures_and_complete_adr0327_options_are_exact :
    (∀ source ∈ selectedFailures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ t o i s, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing⟩

end Tests.ADR0329TwoLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
