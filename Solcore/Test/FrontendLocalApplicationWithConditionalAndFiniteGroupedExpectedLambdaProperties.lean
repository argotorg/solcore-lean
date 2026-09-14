import Solcore.Frontend.LocalApplicationWithConditionalAndFiniteGroupedExpectedLambda
import Solcore.Core.Eval
/-! Independent symbolic consumer for conditional-first finite-group dispatch. -/
set_option autoImplicit false
namespace Tests.ADR0325SymbolicLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"UnifiedLambda", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 325
private def foreignOwner := declaration 9325
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
private def file : Syntax.SourceId := ⟨.main, "unified-lambda.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional (ref (n + 3) "flag") (span (n + 4)) yes (span (n + 5)) no⟩
private def conditionalSource (n : Nat) (yes no : Syntax.Expr) := call n (ref (n + 1) "apply") (conditional n yes no)
private def expectedSource (n : Nat) (ns : List Nat) := call n (ref (n + 1) "apply") (groups ns (lambda (n + 20) "x"))
private def ordinarySource (n : Nat) (ns : List Nat) := call n (ref (n + 1) "apply") (groups ns (ref (n + 20) "ordinary"))
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def expectedCore : Core.Expr := .apply (.var 0) lambdaCore
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private def condCore (yes no : Core.Expr) : Core.Expr := .apply (.var 0) (.ifE (.var 3) yes no)

private theorem applyE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "flag") (.var 3) .bool := .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "ordinary") (.var 4) functionType := .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem wrongE (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "wrong") (.var 5) .word := .pure (.identifier (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "opaque" ≠ "wrong"; decide) (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "flag" ≠ "wrong"; decide) (.tail (by change "ordinary" ≠ "wrong"; decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
private theorem applyC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") = some (.var 0, .function functionType .word) := elaborateRecursiveLocalComputation?_iff.mpr (applyE n)
private theorem flagC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "flag") = some (.var 3, .bool) := elaborateRecursiveLocalComputation?_iff.mpr (flagE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp only [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent, Option.map_none, bind, Option.bind_none]
private theorem lambdaE (n : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambda n name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem groupedOrdinaryE (ns : List Nat) (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (groups ns (ref n "ordinary")) (.var 4) functionType := by
  induction ns with | nil => exact ordinaryE n | cons _ _ ih => exact .group ih
private theorem spineFrom {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) (ns : List Nat) : DirectLambdaGroupSpine (groups ns terminal) (ns.map span) terminal := by
  induction ns with | nil => exact base | cons _ _ ih => exact .group ih
private theorem spine (ns : List Nat) (n : Nat) : DirectLambdaGroupSpine (groups ns (lambda n "x")) (ns.map span) (lambda n "x") := spineFrom .lambda ns
private theorem spineUnique {s a b : Syntax.Expr} {xs ys : List Syntax.SourceSpan} (x : DirectLambdaGroupSpine s xs a) (y : DirectLambdaGroupSpine s ys b) : xs = ys ∧ a = b := by
  induction x generalizing ys b with
  | lambda => cases y; exact ⟨rfl, rfl⟩
  | group _ ih => cases y with | group z => obtain ⟨rfl,rfl⟩ := ih z; exact ⟨rfl,rfl⟩
private theorem shallowFalseFrom (n : Nat) (callee terminal : Syntax.Expr) (ns : List Nat) (base : DirectLambdaGroupSpine terminal [] terminal) (small : ns.length < 3) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (call n callee (groups ns terminal)) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_,_,_,rest,_,other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  have lengths := congrArg List.length (spineUnique (spineFrom base ns) other).1
  simp at lengths; omega
private theorem shallowFalse (n : Nat) (ns : List Nat) (small : ns.length < 3) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (expectedSource n ns) = false := shallowFalseFrom n (ref (n+1) "apply") (lambda (n+20) "x") ns .lambda small
private theorem insideGroups {ns : List Nat} {s t : Syntax.Expr} {ss : List Syntax.SourceSpan} (h : DirectLambdaGroupSpine (groups ns s) ss t) : ∃ tail, DirectLambdaGroupSpine s tail t := by
  induction ns generalizing ss with | nil => exact ⟨ss, h⟩ | cons _ _ ih => cases h with | group child => exact ih child
private theorem ordinaryGroupedFalse (n : Nat) (ns : List Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinarySource n ns) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_,_,_,_,_,outer⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  obtain ⟨_, inner⟩ := insideGroups outer; cases inner
private theorem conditionalGroupedFalse (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (conditionalSource n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_,_,_,_,_,s⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h; cases s

private theorem conditionalE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (selected : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (conditionalSource n yes no) (condCore yc nc) .word := .application selected (applyE (n + 1)) (flagE (n + 3)) ye ne
private theorem groupE (n a b c : Nat) (rest : List Nat) : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (expectedSource n (a :: b :: c :: rest)) expectedCore .word := .application (spine _ _) (applyE (n + 1)) (lambdaE (n + 20) "x")
private theorem directE (n : Nat) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (expectedSource n []) expectedCore .word := .existing rfl (.existing rfl (.expected rfl (.application (applyE (n + 1)) (lambdaE (n + 20) "x"))))
private theorem oneE (n p : Nat) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (expectedSource n [p]) expectedCore .word := .existing rfl (.grouped rfl (.application (applyE (n + 1)) (lambdaE (n + 20) "x")))
private theorem twoE (n p q : Nat) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (expectedSource n [p, q]) expectedCore .word := .twoLevel rfl (.application (applyE (n + 1)) (lambdaE (n + 20) "x"))
private theorem ordinaryOldE (n : Nat) (ns : List Nat) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (ordinarySource n ns) = false) (one : isOneLevelGroupedExpectedLambdaArgumentApplication (ordinarySource n ns) = false) (direct : isDirectExpectedLambdaArgumentApplication (ordinarySource n ns) = false) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (ordinarySource n ns) ordinaryCore .word := by
  apply LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates.existing two
  apply LocalApplicationWithGroupedExpectedLambdaElaborates.existing one
  exact .ordinary direct (.application (applyE (n + 1)) (groupedOrdinaryE ns (n + 20)))
private def allOrdinary := conditionalSource 700 (ref 730 "ordinary") (ref 740 "ordinary")
private def allOrdinaryCore := condCore (.var 4) (.var 4)
private theorem allOrdinaryOldE : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs allOrdinary allOrdinaryCore .word := .existing rfl (.existing rfl (.ordinary rfl (.application (applyE 701) (.conditional (flagE 703) (ordinaryE 730) (ordinaryE 740)))))
private def cLO := conditionalSource 0 (lambda 10 "x") (ref 30 "ordinary")
private def cOL := conditionalSource 40 (ref 70 "ordinary") (lambda 80 "y")
private def cLL := conditionalSource 90 (lambda 100 "x") (lambda 120 "y")
private def cLOCore := condCore lambdaCore (.var 4)
private def cOLCore := condCore (.var 4) lambdaCore
private def cLLCore := condCore lambdaCore lambdaCore
private theorem cLOE : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO cLOCore .word := conditionalE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem cOLE : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL cOLCore .word := conditionalE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem cLLE : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL cLLCore .word := conditionalE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private theorem conditionalContract {s c} (gf : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (child : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) : isConditionalExpectedLambdaArgumentApplication s = true ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = some (c, .word) := by
  let e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word := .conditional child.classified child
  exact ⟨child.classified, gf, child, e, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e⟩
private theorem groupContract {s} (cf : isConditionalExpectedLambdaArgumentApplication s = false) (child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs s expectedCore .word) : isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true ∧ ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs s expectedCore .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s expectedCore .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = some (expectedCore, .word) := by
  let e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s expectedCore .word := .threeOrMoreGrouped cf child.classified child
  exact ⟨cf, child.classified, child, e, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e⟩
private theorem existingContract {s c} (cf : isConditionalExpectedLambdaArgumentApplication s = false) (gf : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (child : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs s c .word) : isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs s c .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = some (c, .word) := by
  let e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c .word := .existing cf gf child
  exact ⟨cf, gf, child, e, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing cf gf, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e⟩
private theorem conditionalCases :
    ∀ item ∈ [(cLO, cLOCore), (cOL, cOLCore), (cLL, cLLCore)], isConditionalExpectedLambdaArgumentApplication item.1 = true ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = false ∧ ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word) := by
  intro item h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl
  · exact conditionalContract (conditionalGroupedFalse _ _ _) cLOE
  · exact conditionalContract (conditionalGroupedFalse _ _ _) cOLE
  · exact conditionalContract (conditionalGroupedFalse _ _ _) cLLE
private theorem groupedCases :
    ∀ item ∈ [(expectedSource 200 [203,204,205], expectedCore), (expectedSource 210 [213,214,215,216], expectedCore), (expectedSource 220 [223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238], expectedCore)], isConditionalExpectedLambdaArgumentApplication item.1 = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = true ∧ ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word) := by
  intro item h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl
  · exact groupContract rfl (groupE 200 203 204 205 [])
  · exact groupContract rfl (groupE 210 213 214 215 [216])
  · exact groupContract rfl (groupE 220 223 224 225 [226,227,228,229,230,231,232,233,234,235,236,237,238])
private theorem existingCases :
    ∀ item ∈ [(expectedSource 300 [], expectedCore), (expectedSource 310 [313], expectedCore), (expectedSource 320 [323,324], expectedCore), (ordinarySource 330 [], ordinaryCore), (ordinarySource 340 [343], ordinaryCore), (ordinarySource 350 [353,354,355], ordinaryCore), (allOrdinary, allOrdinaryCore)], isConditionalExpectedLambdaArgumentApplication item.1 = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word) := by
  intro item h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact existingContract rfl (shallowFalse 300 [] (by decide)) (directE 300)
  · exact existingContract rfl (shallowFalse 310 [313] (by decide)) (oneE 310 313)
  · exact existingContract rfl (shallowFalse 320 [323,324] (by decide)) (twoE 320 323 324)
  · exact existingContract rfl (ordinaryGroupedFalse 330 []) (ordinaryOldE 330 [] rfl rfl rfl)
  · exact existingContract rfl (ordinaryGroupedFalse 340 [343]) (ordinaryOldE 340 [343] rfl rfl rfl)
  · exact existingContract rfl (ordinaryGroupedFalse 350 [353,354,355]) (ordinaryOldE 350 [353,354,355] rfl rfl rfl)
  · exact existingContract rfl (by apply Bool.eq_false_iff.mpr; intro h; obtain ⟨_,_,_,_,_,s⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h; cases s) allOrdinaryOldE

/-- Every source route retains its independently constructed child and exact result. -/
theorem all_three_dispatch_routes_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    (∀ {s c t}, LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs s c t → Core.HasType inputs.context.values c t ∧ ((isConditionalExpectedLambdaArgumentApplication s = true ∧ ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c t) ∨
      (isConditionalExpectedLambdaArgumentApplication s = false ∧ ((isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true ∧ ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs s c t) ∨ (isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs s c t))))) ∧
    (∀ item ∈ [(cLO, cLOCore), (cOL, cOLCore), (cLL, cLLCore)], isConditionalExpectedLambdaArgumentApplication item.1 = true ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = false ∧ ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word)) ∧
    (∀ item ∈ [(expectedSource 200 [203,204,205], expectedCore), (expectedSource 210 [213,214,215,216], expectedCore), (expectedSource 220 [223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238], expectedCore)], isConditionalExpectedLambdaArgumentApplication item.1 = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = true ∧
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word)) ∧
    (∀ item ∈ [(expectedSource 300 [], expectedCore), (expectedSource 310 [313], expectedCore), (expectedSource 320 [323,324], expectedCore), (ordinarySource 330 [], ordinaryCore), (ordinarySource 340 [343], ordinaryCore), (ordinarySource 350 [353,354,355], ordinaryCore), (allOrdinary, allOrdinaryCore)], isConditionalExpectedLambdaArgumentApplication item.1 = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication item.1 = false ∧
      LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧ LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs item.1 item.2 .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs item.1 ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1 = some (item.2, .word)) :=
  ⟨rfl, rfl, fun e => ⟨e.core_hasType, e.provenance⟩, conditionalCases, groupedCases, existingCases⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def env (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private theorem finish {choice : Bool} {argument : Core.Expr} {captured : Core.Environment} (runs : Core.Evaluates (env choice) store argument (.closure .word .word (.var 0) captured) store) : Core.Evaluates (env choice) store (.apply (.var 0) argument) (.word seven) store := .apply (.var rfl) runs (.apply (.var rfl) .word (.var rfl))
private theorem conditionalRuns (choice : Bool) : Core.Evaluates (env choice) store cLOCore (.word seven) store ∧ Core.Evaluates (env choice) store cOLCore (.word seven) store ∧ Core.Evaluates (env choice) store cLLCore (.word seven) store := by
  cases choice
  · exact ⟨finish (.ifFalse (.var rfl) (.var rfl)), finish (.ifFalse (.var rfl) .lambda), finish (.ifFalse (.var rfl) .lambda)⟩
  · exact ⟨finish (.ifTrue (.var rfl) .lambda), finish (.ifTrue (.var rfl) (.var rfl)), finish (.ifTrue (.var rfl) .lambda)⟩
private theorem expectedRuns (choice : Bool) : Core.Evaluates (env choice) store expectedCore (.word seven) store := finish .lambda
private theorem ordinaryRuns (choice : Bool) : Core.Evaluates (env choice) store ordinaryCore (.word seven) store := finish (.var rfl)
private theorem allOrdinaryRuns (choice : Bool) : Core.Evaluates (env choice) store allOrdinaryCore (.word seven) store := by
  cases choice <;> first | exact finish (.ifFalse (.var rfl) (.var rfl)) | exact finish (.ifTrue (.var rfl) (.var rfl))
/-- Every selected Core executes independently and preserves the exact nonempty store. -/
theorem all_selected_cores_execute_without_store_change :
    (∀ choice, Core.Evaluates (env choice) store cLOCore (.word seven) store ∧ Core.Evaluates (env choice) store cOLCore (.word seven) store ∧ Core.Evaluates (env choice) store cLLCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (env choice) store expectedCore (.word seven) store) ∧ (∀ choice, Core.Evaluates (env choice) store ordinaryCore (.word seven) store) ∧ (∀ choice, Core.Evaluates (env choice) store allOrdinaryCore (.word seven) store) := ⟨conditionalRuns, expectedRuns, ordinaryRuns, allOrdinaryRuns⟩

private def badHeader (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n+1)) ⟨span (n+2), []⟩ none (body n "x")⟩
private def badBody (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n+1)) ⟨span (n+2), [⟨span (n+2), .inferred ⟨span (n+2), "x"⟩⟩]⟩ none ⟨span (n+3), [⟨span (n+4), .returnStmt none⟩]⟩⟩
private theorem badHeaderExpectedNone (n : Nat) : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs (badHeader n) functionType = none := by
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
private theorem badBodyExpectedNone (n : Nat) : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs (badBody n) functionType = none := by
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBody functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl
private theorem badHeaderBranchNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badHeader n) functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (badHeader n) = true by rfl]
  exact badHeaderExpectedNone n
private theorem wrongBranchNone (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (ref n "wrong") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (ref n "wrong") = false by rfl]
  simp [wrongC, functionType]
private theorem groupedLambdaRecursiveNone (ns : List Nat) (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (groups ns (lambda n "y")) = none := by
  induction ns with
  | nil => simp [groups, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
  | cons head tail ih => simpa only [groups, List.foldr, elaborateRecursiveLocalComputation?] using ih
private theorem groupedBranchNone (head : Nat) (tail : List Nat) (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (groups (head::tail) (lambda n "y")) functionType = none := by
  have rejected := groupedLambdaRecursiveNone (head::tail) n
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (groups (head::tail) (lambda n "y")) = false by rfl]
  simp [rejected]
private def conditionalFailures := [call 800 (ref 801 "apply") ⟨span 802, .conditional (ref 803 "wrong") (span 804) (lambda 810 "x") (span 805) (ref 820 "ordinary")⟩, conditionalSource 830 (badHeader 840) (ref 850 "ordinary"), conditionalSource 860 (lambda 870 "x") (ref 880 "wrong"), conditionalSource 890 (lambda 900 "x") (groups [910,911,912] (lambda 920 "y")), call 930 (ref 931 "missing") (conditional 930 (lambda 940 "x") (ref 950 "ordinary"))]
private def groupFailures := [call 1000 (ref 1001 "apply") (groups [1003,1004,1005] (badHeader 1010)), call 1020 (ref 1021 "apply") (groups [1023,1024,1025] (badBody 1030)), call 1040 (ref 1041 "flag") (groups [1043,1044,1045] (lambda 1050 "x")), call 1060 (ref 1061 "missing") (groups [1063,1064,1065] (lambda 1070 "x"))]
private theorem selectedGroup {n a b c : Nat} {rest : List Nat} {callee terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (call n callee (groups (a::b::c::rest) terminal)) = true := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mpr ⟨span a, span b, span c, rest.map span, terminal, spineFrom base _⟩
private theorem rejectedGroupArgument (n : Nat) (ns : List Nat) (terminal : Syntax.Expr) (base : DirectLambdaGroupSpine terminal [] terminal) (rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs terminal functionType = none) : elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (call n (ref (n+1) "apply") (groups ns terminal)) = none := by
  apply elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr
  rintro ⟨_,_,e⟩; cases e with | application other callee argument =>
    obtain ⟨_,rfl⟩ := spineUnique (spineFrom base ns) other
    have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
    have a := (elaborateExpectedComputationLambda?_iff (@elaborateRecursiveLocalComputation?_iff)).mpr argument
    rw [rejected] at a; cases a
private theorem groupFailuresChecked : ∀ s ∈ groupFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true ∧ elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs s = none := by
  intro s h; simp only [groupFailures, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨rfl, selectedGroup .lambda, rejectedGroupArgument _ _ _ .lambda (badHeaderExpectedNone _)⟩
  · exact ⟨rfl, selectedGroup .lambda, rejectedGroupArgument _ _ _ .lambda (badBodyExpectedNone _)⟩
  · refine ⟨rfl, selectedGroup .lambda, elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_,_,e⟩; cases e with | application _ c _ => have x := elaborateRecursiveLocalComputation?_iff.mpr c; rw [flagC] at x; cases x
  · refine ⟨rfl, selectedGroup .lambda, elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_,_,e⟩; cases e with | application _ c _ => have x := elaborateRecursiveLocalComputation?_iff.mpr c; rw [missingC] at x; cases x
private def oldFailures := [call 1100 (ref 1101 "apply") (badHeader 1110), call 1120 (ref 1121 "apply") (groups [1123] (badHeader 1130)), call 1140 (ref 1141 "apply") (groups [1143,1144] (badHeader 1150))]
private theorem directBad (n m : Nat) : elaborateExpectedLambdaArgumentApplication? types owner inputs (call n (ref (n+1) "apply") (badHeader m)) = none := by simp only [call, elaborateExpectedLambdaArgumentApplication?, applyC, bind, Option.bind_some, badHeaderExpectedNone, Option.bind_none]
private theorem oneBad (n p m : Nat) : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs (call n (ref (n+1) "apply") (groups [p] (badHeader m))) = none := by simp only [call, groups, List.foldr, elaborateGroupedExpectedLambdaArgumentApplication?, applyC, bind, Option.bind_some, badHeaderExpectedNone, Option.bind_none]
private theorem twoBad (n p q m : Nat) : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (call n (ref (n+1) "apply") (groups [p,q] (badHeader m))) = none := by simp only [call, groups, List.foldr, elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, applyC, bind, Option.bind_some, badHeaderExpectedNone, Option.bind_none]
private theorem oldFailuresChecked : ∀ s ∈ oldFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s = none := by
  intro s h; simp only [oldFailures, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · refine ⟨rfl, shallowFalseFrom 1100 _ _ [] .lambda (by decide), ?_⟩
    rw [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl]
    unfold elaborateLocalApplicationWithExpectedLambda?
    rw [show isDirectExpectedLambdaArgumentApplication (call 1100 (ref 1101 "apply") (badHeader 1110)) = true by rfl]
    exact directBad 1100 1110
  · refine ⟨rfl, shallowFalseFrom 1120 _ _ [1123] .lambda (by decide), ?_⟩
    rw [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl]
    exact oneBad 1120 1123 1130
  · refine ⟨rfl, shallowFalseFrom 1140 _ _ [1143,1144] .lambda (by decide), ?_⟩
    rw [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel rfl]
    exact twoBad 1140 1143 1144 1150
private theorem conditionalFailuresChecked : ∀ s ∈ conditionalFailures, isConditionalExpectedLambdaArgumentApplication s = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs s = none := by
  intro s h; simp only [conditionalFailures, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, elaborateConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
  · rintro ⟨_,_,e⟩; cases e with | application _ _ condition _ _ =>
      have x := elaborateRecursiveLocalComputation?_iff.mpr condition; rw [wrongC] at x; cases x
  · rintro ⟨_,_,e⟩; cases e with | application _ callee _ yes _ =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have x := elaborateConditionalExpectedLambdaBranch?_iff.mpr yes; rw [badHeaderBranchNone] at x; cases x
  · rintro ⟨_,_,e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have x := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [wrongBranchNone] at x; cases x
  · rintro ⟨_,_,e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have x := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedBranchNone] at x; cases x
  · rintro ⟨_,_,e⟩; cases e with | application _ callee _ _ _ =>
      have x := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [missingC] at x; cases x
private def returnedLambda := lambda 1200 "y"
private def returnArgument : Syntax.Expr := ⟨span 1210, .lambda (span 1211) ⟨span 1212, [⟨span 1212, .inferred ⟨span 1212, "x"⟩⟩]⟩ none ⟨span 1213, [⟨span 1214, .returnStmt (some returnedLambda)⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1220, .lambda (span 1221) ⟨span 1222, [⟨span 1222, .inferred ⟨span 1222, "x"⟩⟩]⟩ none ⟨span 1223, [⟨span 1224, .letDecl ⟨span 1225, "y"⟩ none (some returnedLambda)⟩, ⟨span 1226, .returnStmt (some (ref 1227 "x"))⟩]⟩⟩
private def frozenControls := [⟨span 1230, .call (ref 1231 "apply") ⟨span 1232, []⟩⟩, ⟨span 1240, .call (ref 1241 "apply") ⟨span 1242, [lambda 1243 "x", ref 1244 "ordinary"]⟩⟩, groups [1250] (lambda 1251 "x"), call 1260 (ref 1261 "ordinary") (call 1262 (ref 1263 "apply") (lambda 1264 "x")), call 1270 (ref 1271 "apply") ⟨span 1272, .tuple ⟨span 1273, [lambda 1274 "x", ref 1275 "ordinary"]⟩⟩, call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private theorem noSpineFalse (n : Nat) (callee argument : Syntax.Expr) (absent : ¬ ∃ ss terminal, DirectLambdaGroupSpine argument ss terminal) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (call n callee argument) = false := by
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_,_,_,_,_,spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected; exact absent ⟨_,_,spine⟩
private theorem frozenExact {s : Syntax.Expr} (cf : isConditionalExpectedLambdaArgumentApplication s = false) (gf : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) : isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s := ⟨cf, gf, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing cf gf⟩
private theorem frozenControlsChecked : ∀ s ∈ frozenControls, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s := by
  intro s h; simp only [frozenControls, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact frozenExact rfl rfl
  · exact frozenExact rfl rfl
  · exact frozenExact rfl rfl
  · exact frozenExact rfl (noSpineFalse _ _ _ (by rintro ⟨_,_,e⟩; cases e))
  · exact frozenExact rfl (noSpineFalse _ _ _ (by rintro ⟨_,_,e⟩; cases e))
  · exact frozenExact rfl (shallowFalseFrom _ _ _ [] .lambda (by decide))
  · exact frozenExact rfl (shallowFalseFrom _ _ _ [] .lambda (by decide))
private theorem conditionalFailuresFinal : ∀ s ∈ conditionalFailures, isConditionalExpectedLambdaArgumentApplication s = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs s = none ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none := by
  intro s h; have e := conditionalFailuresChecked s h
  exact ⟨e.1, e.2, (elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_conditional e.1).trans e.2⟩
private theorem groupFailuresFinal : ∀ s ∈ groupFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true ∧ elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs s = none ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none := by
  intro s h; have e := groupFailuresChecked s h
  exact ⟨e.1, e.2.1, e.2.2, (elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_threeOrMoreGrouped e.1 e.2.1).trans e.2.2⟩
private theorem oldFailuresFinal : ∀ s ∈ oldFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none := by
  intro s h; have e := oldFailuresChecked s h
  have route := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) e.1 e.2.1
  exact ⟨e.1, e.2.1, route, route.trans e.2.2⟩
/-- Selected failures are final; frozen sources and all complete-Option equations stay exact. -/
theorem recognized_failures_and_frozen_results_are_exact :
    (∀ t o i s, isConditionalExpectedLambdaArgumentApplication s = true →
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? t o i s = elaborateConditionalExpectedLambdaArgumentApplication? t o i s) ∧
    (∀ t o i s, isConditionalExpectedLambdaArgumentApplication s = false → isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true →
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? t o i s = elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? t o i s) ∧
    (∀ t o i s, isConditionalExpectedLambdaArgumentApplication s = false → isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false →
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? t o i s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? t o i s) ∧
    (∀ s ∈ conditionalFailures, isConditionalExpectedLambdaArgumentApplication s = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs s = none ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none) ∧
    (∀ s ∈ groupFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = true ∧ elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs s = none ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none) ∧
    (∀ s ∈ oldFailures, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = none) ∧
    (∀ s ∈ frozenControls, isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs s) :=
  ⟨fun _ _ _ _ => elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_conditional,
    fun _ _ _ _ => elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_threeOrMoreGrouped,
    fun _ _ _ _ => elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing,
    conditionalFailuresFinal, groupFailuresFinal, oldFailuresFinal, frozenControlsChecked⟩
end Tests.ADR0325SymbolicLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaConsumerIndependent
