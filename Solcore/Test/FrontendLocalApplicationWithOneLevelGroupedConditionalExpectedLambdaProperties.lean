import Solcore.Frontend.LocalApplicationWithOneLevelGroupedConditionalExpectedLambda
import Solcore.Core.Machine

/-! Independent symbolic consumer for grouped-conditional-first local applications. -/
set_option autoImplicit false

namespace Tests.ADR0327GroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"GroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 327
private def foreignOwner := declaration 9327
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
private def file : Syntax.SourceId := ⟨.main, "adr0327-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups [n + 5] (conditional n condition yes no))
private def selected (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr := candidate n (ref (n + 1) "apply") (ref (n + 2) "flag") yes no
private def ungrouped (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr := call n (ref (n + 1) "apply") (conditional n (ref (n + 2) "flag") yes no)
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
private theorem ordinaryC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "ordinary") = some (.var 4, functionType) := elaborateRecursiveLocalComputation?_iff.mpr (ordinaryE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent]
private theorem spineFrom {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) (ns : List Nat) : DirectLambdaGroupSpine (groups ns terminal) (ns.map span) terminal := by
  induction ns with | nil => exact base | cons _ _ ih => exact .group ih
private theorem spineUnique {s a b : Syntax.Expr} {xs ys : List Syntax.SourceSpan} (x : DirectLambdaGroupSpine s xs a) (y : DirectLambdaGroupSpine s ys b) : xs = ys ∧ a = b := by
  induction x generalizing ys b with | lambda => cases y; exact ⟨rfl, rfl⟩ | group _ ih => cases y with | group z => obtain ⟨rfl, rfl⟩ := ih z; exact ⟨rfl, rfl⟩
private theorem shallowFalse (n : Nat) (ns : List Nat) (small : ns.length < 3) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (lambdaApplication n ns) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, rest, _, other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  have lengths := congrArg List.length (spineUnique (spineFrom .lambda ns) other).1
  simp at lengths; omega
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem noOldGroup (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child

private def newLO := selected 0 (lambda 10 "x") (ref 30 "ordinary")
private def newOL := selected 40 (ref 70 "ordinary") (lambda 80 "y")
private def newLL := selected 90 (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private theorem makeNew (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem newLOE : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs newLO coreLO .word := makeNew 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem newOLE : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs newOL coreOL .word := makeNew 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem newLLE : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs newLL coreLL .word := makeNew 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl

private def oldConditional := ungrouped 200 (lambda 210 "x") (ref 230 "ordinary")
private def oldGroup := lambdaApplication 300 [303, 304, 305, 306]
private def oldDirect := lambdaApplication 400 []
private def oldDepthOne := lambdaApplication 500 [503]
private def oldDepthTwo := lambdaApplication 600 [603, 604]
private def oldOrdinary := ordinaryApplication 700
private def oldAllOrdinary := selected 800 (ref 830 "ordinary") (ref 840 "ordinary")
private def allOrdinaryCore := conditionalCore (.var 4) (.var 4)
private theorem oldConditionalE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldConditional coreLO .word := .conditional rfl (.application rfl (applyE 201) (flagE 202) (.expected rfl (lambdaE 210 "x")) (.ordinary rfl (ordinaryE 230)))
private theorem oldGroupE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldGroup expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs oldGroup expectedCore .word := .application (spineFrom .lambda [303, 304, 305, 306]) (applyE 301) (lambdaE 320 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem oldDirectE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldDirect expectedCore .word := .existing rfl (shallowFalse 400 [] (by decide)) (.existing rfl (.existing rfl (.expected rfl (.application (applyE 401) (lambdaE 420 "x")))))
private theorem oldDepthOneE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldDepthOne expectedCore .word := .existing rfl (shallowFalse 500 [503] (by decide)) (.existing rfl (.grouped rfl (.application (applyE 501) (lambdaE 520 "x"))))
private theorem oldDepthTwoE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldDepthTwo expectedCore .word := .existing rfl (shallowFalse 600 [603, 604] (by decide)) (.twoLevel rfl (.application (applyE 601) (lambdaE 620 "x")))
private theorem oldOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldOrdinary ordinaryCore .word := .existing rfl (ordinaryFalse 700) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 701) (ordinaryE 720)))))
private theorem oldAllOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs oldAllOrdinary allOrdinaryCore .word := .existing rfl (noOldGroup 800 _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 801) (.group (.conditional (flagE 802) (ordinaryE 830) (ordinaryE 840)))))))

private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop := isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word
private def OldContract (s : Syntax.Expr) (c : Core.Expr) : Prop := isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word
private theorem newContract {s c} (e : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) : NewContract s c := by
  let w : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .oneLevelGroupedConditional e.classified e
  have _ := w.provenance
  exact ⟨e.classified, e, w, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional e.classified, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr w, w.core_hasType⟩
private theorem oldContract {s c} (boundary : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) (e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word) : OldContract s c := by
  let w : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .existing boundary e
  have _ := w.provenance
  exact ⟨boundary, e, w, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing boundary, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr w, w.core_hasType⟩
private theorem newCases : ∀ item ∈ [(newLO, coreLO), (newOL, coreOL), (newLL, coreLL)], NewContract item.1 item.2 := by
  intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> first | exact newContract newLOE | exact newContract newOLE | exact newContract newLLE
private theorem oldCases : ∀ item ∈ [(oldConditional, coreLO), (oldGroup, expectedCore), (oldDirect, expectedCore), (oldDepthOne, expectedCore), (oldDepthTwo, expectedCore), (oldOrdinary, ordinaryCore), (oldAllOrdinary, allOrdinaryCore)], OldContract item.1 item.2 := by
  intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact oldContract rfl oldConditionalE | exact oldContract rfl oldGroupE | exact oldContract rfl oldDirectE | exact oldContract rfl oldDepthOneE | exact oldContract rfl oldDepthTwoE | exact oldContract rfl oldOrdinaryE | exact oldContract rfl oldAllOrdinaryE

/-- Both exact source-dispatch routes retain their complete child, result, and type. -/
theorem exact_two_dispatch_routes_have_complete_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧
    (∀ item ∈ [(newLO, coreLO), (newOL, coreOL), (newLL, coreLL)], NewContract item.1 item.2) ∧
    (∀ item ∈ [(oldConditional, coreLO), (oldGroup, expectedCore), (oldDirect, expectedCore), (oldDepthOne, expectedCore), (oldDepthTwo, expectedCore), (oldOrdinary, ordinaryCore), (oldAllOrdinary, allOrdinaryCore)], OldContract item.1 item.2) := ⟨rfl, rfl, rfl, newCases, oldCases⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) []
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def exactConditionalFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 13 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 14 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private def exactLambdaFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 10 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 11 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private theorem conditionalFuels : ∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core := by
  intro choice core member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩
private theorem lambdaFuels : ∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core := by
  intro choice core member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩

/-- Every selected Core has its exact predecessor fuel boundary and literal store. -/
theorem all_selected_cores_have_exact_fuel_and_store :
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core) := ⟨conditionalFuels, lambdaFuels⟩

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
  have nested : elaborateRecursiveLocalComputation? inputs.names inputs.context (nestedLambdaCall n) = none := by simp [nestedLambdaCall, call, elaborateRecursiveLocalComputation?, ordinaryC, argument]
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (nestedLambdaCall n) = false by rfl]
  simp [nested]
private def failures := [candidate 900 (ref 901 "apply") (ref 902 "wrong") (lambda 910 "x") (ref 920 "ordinary"), candidate 930 (ref 931 "apply") (ref 932 "missing") (lambda 940 "x") (ref 950 "ordinary"), selected 960 (badHeader 970) (ref 980 "ordinary"), selected 990 (badBody 1000) (ref 1010 "ordinary"), selected 1020 (lambda 1030 "x") (ref 1040 "wrong"), selected 1050 (lambda 1060 "x") (ref 1070 "missing"), candidate 1080 (ref 1081 "flag") (ref 1082 "flag") (lambda 1090 "x") (ref 1100 "ordinary"), candidate 1110 (ref 1111 "missing") (ref 1112 "flag") (lambda 1120 "x") (ref 1130 "ordinary"), selected 1140 (lambda 1150 "x") (groups [1160] (lambda 1170 "y")), selected 1180 (lambda 1190 "x") (nestedLambdaCall 1200)]
private theorem failuresFinal : ∀ source ∈ failures, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [failures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, groups, conditional, call, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem wrapperFailuresFinal : ∀ source ∈ failures, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member
  have e := failuresFinal source member
  exact ⟨e.1, e.2, (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional e.1).trans e.2⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private def inheritedFailures := [ungrouped 1300 (badHeader 1310) (ref 1320 "ordinary"), call 1330 (ref 1331 "apply") (groups [1333, 1334, 1335] (badHeader 1340)), call 1350 (ref 1351 "apply") (groups [1353, 1354] (badHeader 1360)), call 1370 (ref 1371 "apply") (groups [1373] (badHeader 1380)), call 1390 (ref 1391 "apply") (badHeader 1400)]
private def boundaryControls := [call 1410 (ref 1411 "apply") (groups [1413, 1414] (conditional 1410 (ref 1412 "flag") (lambda 1420 "x") (ref 1430 "ordinary"))), selected 1440 (groups [1450] (lambda 1460 "x")) (ref 1470 "ordinary"), ⟨span 1480, .call (ref 1481 "apply") ⟨span 1482, []⟩⟩, ⟨span 1490, .call (ref 1491 "apply") ⟨span 1492, [lambda 1493 "x", ref 1494 "ordinary"]⟩⟩, conditional 1500 (ref 1502 "flag") (lambda 1510 "x") (ref 1520 "ordinary"), call 1530 (ref 1531 "apply") ⟨span 1532, .tuple ⟨span 1533, [lambda 1540 "x", ref 1550 "ordinary"]⟩⟩, call 1560 (ref 1561 "ordinary") (call 1562 (ref 1563 "apply") (lambda 1564 "x")), call 1570 (ref 1571 "apply") returnArgument, call 1580 (ref 1581 "apply") letArgument]
private theorem falseSourcesExact : ∀ source ∈ inheritedFailures ++ boundaryControls, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs source := by
  intro source member; simp only [List.mem_append, inheritedFailures, boundaryControls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨rfl, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing rfl⟩

/-- Recognized new failures are final; every false source retains the whole ADR-0325 Option. -/
theorem recognized_failures_and_predecessor_complete_options_are_exact :
    (∀ source ∈ failures, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ source ∈ inheritedFailures ++ boundaryControls, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs source) ∧
    (∀ t o i s, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? t o i s) := ⟨wrapperFailuresFinal, falseSourcesExact, fun _ _ _ _ => elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing⟩

end Tests.ADR0327GroupedConditionalFirstWrapperSymbolicConsumerIndependent
