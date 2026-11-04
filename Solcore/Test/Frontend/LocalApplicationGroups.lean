import Solcore.Frontend.LocalApplication
import Solcore.Core.Eval
import Solcore.Core.Machine
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
# Local application wrapper tests

Local applications with expected lambdas and grouped conditionals, one consumer per wrapper of the
source-disjoint dispatcher.
-/

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithExpectedLambdaProperties
/-! Independent symbolic consumer for the source-disjoint local-application dispatcher. -/
set_option autoImplicit false
namespace Tests.ADR0318LocalApplicationWithExpectedLambdaConsumer
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LocalExpectedApplication", by decide⟩], by decide⟩⟩, index⟩
private def owner : Resolved.DeclarationId := declaration 318
private def foreignOwner : Resolved.DeclarationId := declaration 9318
private def applyId : Resolved.LocalId := ⟨owner, 17⟩
private def opaqueId : Resolved.LocalId := ⟨foreignOwner, 700⟩
private def duplicateId : Resolved.LocalId := ⟨owner, 3⟩
private def flagId : Resolved.LocalId := ⟨foreignOwner, 701⟩
private def ordinaryId : Resolved.LocalId := ⟨owner, 29⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell (.function .word .unit)⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩
], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "local-expected-application.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def body : Syntax.Block :=
  ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr :=
  ⟨span 3, .lambda (span 4)
    ⟨span 5, [⟨span 5, .inferred ⟨span 5, "x"⟩⟩]⟩ none body⟩
private def directSource : Syntax.Expr :=
  ⟨span 0, .call (ref 1 "apply") ⟨span 2, [argument]⟩⟩
private def directCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryArgument : Syntax.Expr := ref 20 "ordinary"
private def ordinarySource : Syntax.Expr :=
  ⟨span 17, .call (ref 18 "apply") ⟨span 19, [ordinaryArgument]⟩⟩
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem directCalleeElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 1 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem directArgumentElaboration :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs argument (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, body, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem directExpectedElaboration :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs directSource directCore .word :=
  .application directCalleeElaboration directArgumentElaboration

private theorem ordinaryCalleeElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 18 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem ordinaryArgumentElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      ordinaryArgument (.var 4) functionType := by
  exact .pure
    (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))

private theorem ordinaryRecursiveElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      ordinarySource ordinaryCore .word :=
  .application ordinaryCalleeElaboration ordinaryArgumentElaboration

private theorem directCombinedElaboration :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs directSource directCore .word :=
  .expected rfl directExpectedElaboration

private theorem ordinaryCombinedElaboration :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs ordinarySource ordinaryCore .word :=
  .ordinary rfl ordinaryRecursiveElaboration

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def duplicateValue : Core.Value := .cellRef (.function .unit .word) 31
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def environment : Core.Environment :=
  [applyValue, opaqueValue, duplicateValue, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

theorem independently_executed_direct_branch :
    Core.Evaluates environment store directCore (.word seven) store := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))

theorem direct_and_ordinary_paths_are_disjoint :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧
    inputs.names[2]? = some ("apply", duplicateId) ∧
    isDirectExpectedLambdaArgumentApplication directSource = true ∧
    isDirectExpectedLambdaArgumentApplication ordinarySource = false ∧
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs directSource directCore .word ∧
    RecursiveLocalComputationElaborates
      inputs.names inputs.context ordinarySource ordinaryCore .word ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs directSource directCore .word ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs ordinarySource ordinaryCore .word ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs directSource =
      some (directCore, .word) ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs ordinarySource =
      some (ordinaryCore, .word) ∧
    Core.HasType inputs.context.values directCore .word ∧
    Core.HasType inputs.context.values ordinaryCore .word ∧
    ((isDirectExpectedLambdaArgumentApplication directSource = true ∧
        ExpectedLambdaArgumentApplicationElaborates
          types owner inputs directSource directCore .word) ∨
      (isDirectExpectedLambdaArgumentApplication directSource = false ∧
        ∃ callSpan argumentsSpan callee argument,
          directSource = ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
          RecursiveLocalComputationElaborates
            inputs.names inputs.context directSource directCore .word)) ∧
    ((isDirectExpectedLambdaArgumentApplication ordinarySource = true ∧
        ExpectedLambdaArgumentApplicationElaborates
          types owner inputs ordinarySource ordinaryCore .word) ∨
      (isDirectExpectedLambdaArgumentApplication ordinarySource = false ∧
        ∃ callSpan argumentsSpan callee argument,
          ordinarySource = ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
          RecursiveLocalComputationElaborates
            inputs.names inputs.context ordinarySource ordinaryCore .word)) ∧
    ¬ (isDirectExpectedLambdaArgumentApplication directSource = true ∧
      isDirectExpectedLambdaArgumentApplication directSource = false) ∧
    ¬ (isDirectExpectedLambdaArgumentApplication ordinarySource = true ∧
      isDirectExpectedLambdaArgumentApplication ordinarySource = false) := by
  have directChecked :=
    elaborateLocalApplicationWithExpectedLambda?_iff.mpr directCombinedElaboration
  have ordinaryChecked :=
    elaborateLocalApplicationWithExpectedLambda?_iff.mpr ordinaryCombinedElaboration
  have directRestored :=
    elaborateLocalApplicationWithExpectedLambda?_iff.mp directChecked
  have ordinaryRestored :=
    elaborateLocalApplicationWithExpectedLambda?_iff.mp ordinaryChecked
  have directProvenance := directRestored.provenance
  have ordinaryProvenance := ordinaryRestored.provenance
  exact ⟨rfl, rfl, rfl, rfl, directExpectedElaboration,
    ordinaryRecursiveElaboration, directRestored, ordinaryRestored,
    directChecked, ordinaryChecked, directRestored.core_hasType,
    ordinaryRestored.core_hasType, directProvenance, ordinaryProvenance,
    by simp, by simp⟩

private def malformedArgument : Syntax.Expr :=
  ⟨span 31, .lambda (span 32) ⟨span 33, []⟩ none
    ⟨span 34, [⟨span 35, .returnStmt none⟩]⟩⟩
private def malformedSource : Syntax.Expr :=
  ⟨span 28, .call (ref 29 "apply") ⟨span 30, [malformedArgument]⟩⟩

private theorem malformedExpectedRejected :
    elaborateExpectedLambdaArgumentApplication?
      types owner inputs malformedSource = none := by
  have calleeChecked : elaborateRecursiveLocalComputation? inputs.names inputs.context
      (ref 29 "apply") = some (.var 0, .function functionType .word) :=
    elaborateRecursiveLocalComputation?_iff.mpr
      (show RecursiveLocalComputationElaborates inputs.names inputs.context
        (ref 29 "apply") (.var 0) (.function functionType .word) from
        .pure (.identifier .head) (.var .head) (.var .head))
  have noHeader : declareExpectedUnaryLambdaHeader?
      types owner inputs malformedArgument functionType = none := rfl
  simp only [malformedSource, elaborateExpectedLambdaArgumentApplication?, calleeChecked,
    bind, Option.bind_some, elaborateExpectedComputationLambda?, noHeader,
    Option.bind_none]

private theorem malformedOrdinaryRejected :
    elaborateRecursiveLocalComputation?
      inputs.names inputs.context malformedSource = none := by
  simp [malformedSource, malformedArgument, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]

theorem recognized_lambda_failure_never_falls_back :
    isDirectExpectedLambdaArgumentApplication malformedSource = true ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs malformedSource = none ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context malformedSource = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs malformedSource = none ∧
    ¬ ∃ core type,
      LocalApplicationWithExpectedLambdaElaborates
        types owner inputs malformedSource core type := by
  have combinedRejected : elaborateLocalApplicationWithExpectedLambda?
      types owner inputs malformedSource = none := by
    change (if isDirectExpectedLambdaArgumentApplication malformedSource then
      elaborateExpectedLambdaArgumentApplication? types owner inputs malformedSource
    else elaborateRecursiveLocalComputation? inputs.names inputs.context malformedSource) = none
    rw [show isDirectExpectedLambdaArgumentApplication malformedSource = true by rfl]
    exact malformedExpectedRejected
  exact ⟨rfl, malformedExpectedRejected, malformedOrdinaryRejected, combinedRejected,
    elaborateLocalApplicationWithExpectedLambda?_eq_none_iff.mp combinedRejected⟩

private def groupedLambdaArgumentSource : Syntax.Expr :=
  ⟨span 40, .call (ref 41 "apply")
    ⟨span 42, [⟨span 43, .group argument⟩]⟩⟩
private def nestedLambdaApplication : Syntax.Expr :=
  ⟨span 44, .call (ref 45 "apply") ⟨span 46, [argument]⟩⟩
private def nestedLambdaApplicationArgumentSource : Syntax.Expr :=
  ⟨span 47, .call (ref 48 "ordinary")
    ⟨span 49, [nestedLambdaApplication]⟩⟩
private def tupleLambdaArgumentSource : Syntax.Expr :=
  ⟨span 50, .call (ref 51 "apply")
    ⟨span 52, [⟨span 53, .tuple ⟨span 54, [argument, ordinaryArgument]⟩⟩]⟩⟩
private def conditionalLambdaArgumentSource : Syntax.Expr :=
  ⟨span 55, .call (ref 56 "apply") ⟨span 57,
    [⟨span 58, .conditional (ref 59 "flag") (span 60)
      argument (span 61) ordinaryArgument⟩]⟩⟩
private def zeroArgumentSource : Syntax.Expr :=
  ⟨span 62, .call (ref 63 "apply") ⟨span 64, []⟩⟩
private def multipleArgumentSource : Syntax.Expr :=
  ⟨span 65, .call (ref 66 "apply") ⟨span 67, [argument, ordinaryArgument]⟩⟩

private theorem groupedLambdaArgumentRejected :
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs groupedLambdaArgumentSource = none := by
  change (if isDirectExpectedLambdaArgumentApplication groupedLambdaArgumentSource then
    elaborateExpectedLambdaArgumentApplication? types owner inputs groupedLambdaArgumentSource else
    elaborateRecursiveLocalComputation? inputs.names inputs.context groupedLambdaArgumentSource) = none
  rw [show isDirectExpectedLambdaArgumentApplication groupedLambdaArgumentSource = false by rfl]
  simp [groupedLambdaArgumentSource, argument, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]

private theorem nestedLambdaApplicationArgumentRejected :
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs nestedLambdaApplicationArgumentSource = none := by
  change (if isDirectExpectedLambdaArgumentApplication nestedLambdaApplicationArgumentSource
    then elaborateExpectedLambdaArgumentApplication? types owner inputs nestedLambdaApplicationArgumentSource
    else elaborateRecursiveLocalComputation? inputs.names inputs.context nestedLambdaApplicationArgumentSource) = none
  rw [show isDirectExpectedLambdaArgumentApplication nestedLambdaApplicationArgumentSource = false by rfl]
  simp [nestedLambdaApplicationArgumentSource, nestedLambdaApplication, argument, ref,
    elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]

private theorem tupleLambdaArgumentRejected :
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs tupleLambdaArgumentSource = none := by
  change (if isDirectExpectedLambdaArgumentApplication tupleLambdaArgumentSource then
    elaborateExpectedLambdaArgumentApplication? types owner inputs tupleLambdaArgumentSource else
    elaborateRecursiveLocalComputation? inputs.names inputs.context tupleLambdaArgumentSource) = none
  rw [show isDirectExpectedLambdaArgumentApplication tupleLambdaArgumentSource = false by rfl]
  simp [tupleLambdaArgumentSource, argument, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]

private theorem conditionalLambdaArgumentRejected :
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs conditionalLambdaArgumentSource = none := by
  change (if isDirectExpectedLambdaArgumentApplication conditionalLambdaArgumentSource
    then elaborateExpectedLambdaArgumentApplication? types owner inputs conditionalLambdaArgumentSource
    else elaborateRecursiveLocalComputation? inputs.names inputs.context conditionalLambdaArgumentSource) = none
  rw [show isDirectExpectedLambdaArgumentApplication conditionalLambdaArgumentSource = false by rfl]
  simp [conditionalLambdaArgumentSource, argument, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]

theorem unsupported_shapes_remain_exact_absence :
    isDirectExpectedLambdaArgumentApplication groupedLambdaArgumentSource = false ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs groupedLambdaArgumentSource = none ∧
    isDirectExpectedLambdaArgumentApplication nestedLambdaApplicationArgumentSource = false ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs nestedLambdaApplicationArgumentSource = none ∧
    isDirectExpectedLambdaArgumentApplication tupleLambdaArgumentSource = false ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs tupleLambdaArgumentSource = none ∧
    isDirectExpectedLambdaArgumentApplication conditionalLambdaArgumentSource = false ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs conditionalLambdaArgumentSource = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs zeroArgumentSource = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs multipleArgumentSource = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs argument = none := by
  exact ⟨rfl, groupedLambdaArgumentRejected, rfl,
    nestedLambdaApplicationArgumentRejected, rfl, tupleLambdaArgumentRejected, rfl,
    conditionalLambdaArgumentRejected, rfl, rfl, rfl⟩

end Tests.ADR0318LocalApplicationWithExpectedLambdaConsumer
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaProperties
/-! Independent symbolic consumer for the ADR-0334-first ADR-0333 wrapper. -/
set_option autoImplicit false
namespace Tests.ADR0335FiveLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FiveGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 335
private def foreignOwner := declaration 9335
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
private def file : Syntax.SourceId := ⟨.main, "adr0335-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6, n + 7, n + 8, n + 9] callee condition yes no
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
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ((isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = none
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group innermost => cases innermost with | group final => cases final
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by intro ns; induction ns with | nil => intro _ _ spine; cases spine | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem oldConditionalNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]
  simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl
  all_goals apply oldConditionalNone _ _ _ _ rfl rfl (noFiniteAt _ _ _ _) rfl rfl rfl <;> simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem newContract {s c} (e : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : NewContract s c := by
  have four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have two : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) two
  have current := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) three
  have latest := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  let wrapped : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .fiveLevelGroupedConditional e.classified e
  refine ⟨e.classified, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional e.classified, elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, wrapped.core_hasType, ⟨wrapped.provenance, e.provenance⟩, latest, latest.trans (current.trans (previous.trans oldNone))⟩
/-! The five-group selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_five_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact newContract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact newContract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))
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
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member; have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) h.1
  exact ⟨h.1, h.2, route, route.trans h.2⟩
private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private def threeGroupControl := selectedAt 720 [725, 726, 727] (lambda 730 "x") (ref 750 "ordinary")
private def fourGroupControl := selectedAt 750 [755, 756, 757, 758] (lambda 760 "x") (ref 780 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
private theorem threeGroupE : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs threeGroupControl coreLO .word := .application rfl (applyE 721) (flagE 722) (.expected rfl (lambdaE 730 "x")) (.ordinary rfl (ordinaryE 750))
private theorem fourGroupE : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fourGroupControl coreLO .word := .application rfl (applyE 751) (flagE 752) (.expected rfl (lambdaE 760 "x")) (.ordinary rfl (ordinaryE 780))
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
private theorem lambda4E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := .application (spineFrom .lambda [743, 744, 745, 746]) (applyE 741) (lambdaE 760 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda5E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := .application (spineFrom .lambda [773, 774, 775, 776, 777]) (applyE 771) (lambdaE 790 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda6E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := .application (spineFrom .lambda [798, 799, 800, 801, 802, 803]) (applyE 796) (lambdaE 815 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing four (.existing three e))
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e) three four
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing four).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans ((elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old))
private theorem currentThreeCheck : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs threeGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.threeLevelGroupedConditional threeGroupE.classified threeGroupE))
private theorem currentFourCheck : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs fourGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.fourLevelGroupedConditional fourGroupE.classified fourGroupE)
private def sixGroupConditional := selectedAt 760 [765, 766, 767, 768, 769, 770] (lambda 780 "x") (ref 800 "ordinary")
private def allOrdinarySource := selectedAt 810 [815, 816, 817, 818, 819] (ref 820 "ordinary") (ref 830 "ordinary")
private def groupedOnlySource := selectedAt 840 [845, 846, 847, 848, 849] (groups [850] (lambda 860 "x")) (ref 880 "ordinary")
private def nestedOnlySource := selectedAt 890 [895, 896, 897, 898, 899] (nestedLambdaCall 900) (ref 920 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 810 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 811) (.group (.group (.group (.group (.group (.conditional (flagE 812) (ordinaryE 820) (ordinaryE 830)))))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (sixGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type)) ∧ ((isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); let wrapped : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child; exact ⟨wrapped, child, wrapped.provenance, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (currentOldCheck rfl (.existing rfl immediateE) rfl)
  · exact completeOption (currentOldCheck rfl oneGroupE rfl)
  · exact completeOption (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))
  · exact completeOption currentThreeCheck
  · exact completeOption currentFourCheck
  · exact completeOption (currentOldNone rfl (by simpa only [sixGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768, 769, 770] (lambda 780 "x") (ref 800 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl)
  · exact completeOption (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 840 [845, 846, 847, 848, 849] (groups [850] (lambda 860 "x")) (ref 880 "ordinary") rfl rfl (noFiniteAt 840 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 890 [895, 896, 897, 898, 899] (nestedLambdaCall 900) (ref 920 "ordinary") rfl rfl (noFiniteAt 890 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda0E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda1E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda2E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda3E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda4E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda5E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda6E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl)
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional eLO.classified eLO) | exact elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional eOL.classified eOL) | exact elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional eLL.classified eLL) | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousFourConditionalCurrentNone : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary")) = none := by rw [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional (by rfl)]; simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousThreeConditionalCurrentNone : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary")) = none := by rw [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (by rfl)]; simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousTwoConditionalCurrentNone : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary")) = none := by rw [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional (by rfl)]; simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
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
private def inheritedAndBoundaryFailures := [selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary"), selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary"), selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary"), selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private def InheritedFailure (source : Syntax.Expr) : Prop := isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := by have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary; exact ⟨boundary, rejected, current, route, route.trans current⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousFourConditionalCurrentNone
  · exact inherit ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousThreeConditionalCurrentNone)
  · exact inherit ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone))
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)
/-! Selected failures are final; every false neighbor retains the complete ADR-0333 Option. -/
theorem selected_failures_and_complete_adr0333_options_are_exact :
    (∀ source ∈ selectedFailures, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing⟩
end Tests.ADR0335FiveLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithFourLevelGroupedConditionalExpectedLambdaProperties
/-! Independent symbolic consumer for the ADR-0332-first ADR-0331 wrapper. -/
set_option autoImplicit false

namespace Tests.ADR0333FourLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FourGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 333
private def foreignOwner := declaration 9333
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
private def file : Syntax.SourceId := ⟨.main, "adr0333-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6, n + 7, n + 8] callee condition yes no
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
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  ((isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = none
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group final => cases final
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by intro ns; induction ns with | nil => intro _ _ spine; cases spine | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem oldConditionalNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]
  simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl
  all_goals apply oldConditionalNone _ _ _ _ rfl rfl (noFiniteAt _ _ _ _) rfl rfl rfl <;> simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem newContract {s c} (e : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : NewContract s c := by
  have three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have two : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) two
  have current := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) three
  let wrapped : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .fourLevelGroupedConditional e.classified e
  refine ⟨e.classified, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional e.classified, elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, wrapped.core_hasType, ⟨wrapped.provenance, e.provenance⟩, current, current.trans (previous.trans oldNone)⟩
/-! The four-group selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_four_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact newContract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact newContract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))

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
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) h.1
  exact ⟨h.1, h.2, route, route.trans h.2⟩

private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private def threeGroupControl := selectedAt 720 [725, 726, 727] (lambda 730 "x") (ref 750 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
private theorem threeGroupE : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs threeGroupControl coreLO .word := .application rfl (applyE 721) (flagE 722) (.expected rfl (lambdaE 730 "x")) (.ordinary rfl (ordinaryE 750))
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
private theorem lambda4E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := .application (spineFrom .lambda [743, 744, 745, 746]) (applyE 741) (lambdaE 760 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda5E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := .application (spineFrom .lambda [773, 774, 775, 776, 777]) (applyE 771) (lambdaE 790 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr e)
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e) three
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans ((elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old)
private theorem currentThreeCheck : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs threeGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr (.threeLevelGroupedConditional threeGroupE.classified threeGroupE)
private def fiveGroupConditional := selectedAt 760 [765, 766, 767, 768, 769] (lambda 780 "x") (ref 800 "ordinary")
private def allOrdinarySource := selectedAt 810 [815, 816, 817, 818] (ref 820 "ordinary") (ref 830 "ordinary")
private def groupedOnlySource := selectedAt 840 [845, 846, 847, 848] (groups [850] (lambda 860 "x")) (ref 880 "ordinary")
private def nestedOnlySource := selectedAt 890 [895, 896, 897, 898] (nestedLambdaCall 900) (ref 920 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 810 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 811) (.group (.group (.group (.group (.conditional (flagE 812) (ordinaryE 820) (ordinaryE 830))))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fiveGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type)) ∧ ((isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); let wrapped : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child; exact ⟨wrapped, child, wrapped.provenance, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (currentOldCheck rfl (.existing rfl immediateE) rfl)
  · exact completeOption (currentOldCheck rfl oneGroupE rfl)
  · exact completeOption (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))
  · exact completeOption currentThreeCheck
  · exact completeOption (currentOldNone rfl (by simpa only [fiveGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768, 769] (lambda 780 "x") (ref 800 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl)
  · exact completeOption (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 840 [845, 846, 847, 848] (groups [850] (lambda 860 "x")) (ref 880 "ordinary") rfl rfl (noFiniteAt 840 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 890 [895, 896, 897, 898] (nestedLambdaCall 900) (ref 920 "ordinary") rfl rfl (noFiniteAt 890 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda0E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda1E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda2E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda3E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda4E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda5E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl)
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.fourLevelGroupedConditional eLO.classified eLO) | exact elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.fourLevelGroupedConditional eOL.classified eOL) | exact elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr (.fourLevelGroupedConditional eLL.classified eLL) | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousThreeConditionalCurrentNone : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary")) = none := by rw [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (by rfl)]; simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousTwoConditionalCurrentNone : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary")) = none := by rw [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional (by rfl)]; simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
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
private def inheritedAndBoundaryFailures := [selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary"), selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary"), selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private def InheritedFailure (source : Syntax.Expr) : Prop := isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := by have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary; exact ⟨boundary, rejected, current, route, route.trans current⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousThreeConditionalCurrentNone
  · exact inherit ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone)
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)

/-! Selected failures are final; every false neighbor retains the complete ADR-0331 Option. -/
theorem selected_failures_and_complete_adr0331_options_are_exact :
    (∀ source ∈ selectedFailures, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing⟩

end Tests.ADR0333FourLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithGroupedExpectedLambdaProperties
/-! Independent symbolic consumer for the group-first local-application entry. -/
set_option autoImplicit false
namespace Tests.ADR0320SymbolicLocalApplicationWithGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"GroupFirstApplication",by decide⟩],by decide⟩⟩,index⟩
private def owner : Resolved.DeclarationId := declaration 320
private def foreignOwner : Resolved.DeclarationId := declaration 9320
private def applyId : Resolved.LocalId := ⟨owner, 17⟩
private def opaqueId : Resolved.LocalId := ⟨foreignOwner, 700⟩
private def duplicateId : Resolved.LocalId := ⟨owner, 3⟩
private def flagId : Resolved.LocalId := ⟨foreignOwner, 701⟩
private def ordinaryId : Resolved.LocalId := ⟨owner, 29⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply",applyId,.function functionType .word⟩,
  ⟨"opaque",opaqueId,.cell (.function .word .unit)⟩,⟨"apply",duplicateId,.unit⟩,
  ⟨"flag",flagId,.bool⟩,⟨"ordinary",ordinaryId,functionType⟩],by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "group-first-application.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n,.identifier ⟨span (n+1),name⟩⟩
private def body : Syntax.Block := ⟨span 6,[⟨span 7,.returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr := ⟨span 4,.lambda (span 5)
  ⟨span 6,[⟨span 6,.inferred ⟨span 6,"x"⟩⟩]⟩ none body⟩
private def groupedSource : Syntax.Expr := ⟨span 0,.call (ref 1 "apply")
  ⟨span 2,[⟨span 3,.group argument⟩]⟩⟩
private def directSource : Syntax.Expr := ⟨span 10,.call (ref 11 "apply") ⟨span 12,[argument]⟩⟩
private def ordinaryArgument : Syntax.Expr := ref 14 "ordinary"
private def ordinarySource : Syntax.Expr := ⟨span 15,.call (ref 16 "apply") ⟨span 17,[ordinaryArgument]⟩⟩
private def groupedOrdinarySource : Syntax.Expr := ⟨span 18,.call (ref 19 "apply")
  ⟨span 20,[⟨span 21,.group ordinaryArgument⟩]⟩⟩
private def lambdaCore : Core.Expr := .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide)
      (.tail (by change "opaque" ≠ "flag"; decide)
      (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
private theorem innerLambdaElaboration : ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs argument
      (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner "x" .word,body,.word,.word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem groupedChild : GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word :=
  .application (applyElaboration 1) innerLambdaElaboration
private theorem directChild : ExpectedLambdaArgumentApplicationElaborates types owner inputs directSource lambdaCore .word :=
  .application (applyElaboration 11) innerLambdaElaboration
private theorem ordinaryChild : RecursiveLocalComputationElaborates inputs.names inputs.context ordinarySource ordinaryCore .word :=
  .application (applyElaboration 16) (ordinaryElaboration 14)
private theorem groupedOrdinaryChild : RecursiveLocalComputationElaborates inputs.names inputs.context groupedOrdinarySource ordinaryCore .word :=
  .application (applyElaboration 19) (.group (ordinaryElaboration 14))
private theorem directExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := .expected rfl directChild
private theorem ordinaryExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := .ordinary rfl ordinaryChild
private theorem groupedOrdinaryExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word :=
  .ordinary rfl groupedOrdinaryChild
private theorem groupedSelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedSource lambdaCore .word := .grouped rfl groupedChild
private theorem directSelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := .existing rfl directExisting
private theorem ordinarySelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := .existing rfl ordinaryExisting
private theorem groupedOrdinarySelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word :=
  .existing rfl groupedOrdinaryExisting
private theorem groupedProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
    GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word := by
  rcases groupedSelected.provenance with h | h
  · exact h
  · cases h.1
private theorem directProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := by
  rcases directSelected.provenance with h | h
  · cases h.1
  · exact h
private theorem ordinaryProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := by
  rcases ordinarySelected.provenance with h | h
  · cases h.1
  · exact h
private theorem groupedOrdinaryProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word := by
  rcases groupedOrdinarySelected.provenance with h | h
  · cases h.1
  · exact h
theorem all_four_source_disjoint_paths_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedSource lambdaCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs directSource lambdaCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedSource = some (lambdaCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs directSource = some (lambdaCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs ordinarySource = some (ordinaryCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedOrdinarySource = some (ordinaryCore,.word) ∧
    Core.HasType inputs.context.values lambdaCore .word ∧ Core.HasType inputs.context.values ordinaryCore .word ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
      GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedSource =
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedSource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs directSource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs directSource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs ordinarySource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs ordinarySource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedOrdinarySource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedOrdinarySource := by
  have g := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedSelected
  have d := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr directSelected
  have o := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr ordinarySelected
  have go := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedOrdinarySelected
  have gr := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp g
  have dr := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp d
  have or := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp o
  have gor := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp go
  change (["apply","opaque","apply","flag","ordinary"].zip
    [applyId,opaqueId,duplicateId,flagId,ordinaryId])[1]?.map Prod.snd = some opaqueId ∧ _
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, gr, dr, or, gor, g, d, o, go,
    gr.core_hasType, or.core_hasType, groupedProvenance, directProvenance,
    ordinaryProvenance, groupedOrdinaryProvenance,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def duplicateValue : Core.Value := .cellRef (.function .unit .word) 31
private def ordinaryValue : Core.Value := .closure .word .word (.var 0)
  [.hostFunction .storageRead]
private def applyValue : Core.Value := .closure functionType .word
  (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment : Core.Environment :=
  [applyValue, opaqueValue, duplicateValue, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_selected_core :
    Core.Evaluates environment store lambdaCore (.word seven) store := by
  exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def groupedCall (n : Nat) (callee child : Syntax.Expr) : Syntax.Expr := ⟨span n,.call callee ⟨span (n+1),[⟨span (n+2),.group child⟩]⟩⟩
private def badHeaderArgument : Syntax.Expr := ⟨span 30,.lambda (span 31) ⟨span 32,[]⟩ none body⟩
private def badHeader := groupedCall 33 (ref 34 "apply") badHeaderArgument
private def badBodyArgument : Syntax.Expr := ⟨span 37,.lambda (span 38)
  ⟨span 39,[⟨span 39,.inferred ⟨span 39,"x"⟩⟩]⟩ none ⟨span 40,[⟨span 41,.returnStmt none⟩]⟩⟩
private def badBody := groupedCall 42 (ref 43 "apply") badBodyArgument
private def nonFunction := groupedCall 46 (ref 47 "flag") argument
private def malformedDirect : Syntax.Expr := ⟨span 50,.call (ref 51 "apply") ⟨span 52,[badHeaderArgument]⟩⟩
private def doubleGroup : Syntax.Expr := groupedCall 53 (ref 54 "apply") ⟨span 56,.group argument⟩
private def innerCall : Syntax.Expr := ⟨span 57,.call (ref 58 "apply") ⟨span 59,[argument]⟩⟩
private def nestedSource : Syntax.Expr := ⟨span 60,.call (ref 61 "ordinary") ⟨span 62,[innerCall]⟩⟩
private def groupedTuple : Syntax.Expr := groupedCall 63 (ref 64 "apply")
  ⟨span 66, .tuple ⟨span 67, [argument, ordinaryArgument]⟩⟩
private def groupedConditional : Syntax.Expr := groupedCall 68 (ref 69 "apply")
  ⟨span 71, .conditional (ref 72 "flag") (span 73) argument (span 74) ordinaryArgument⟩
private def callInsideGroup : Syntax.Expr := groupedCall 75 (ref 76 "ordinary") innerCall
private def zeroArguments : Syntax.Expr := ⟨span 78,.call (ref 79 "apply") ⟨span 80,[]⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 81,.call (ref 82 "apply") ⟨span 83,[⟨span 84,.group argument⟩,argument]⟩⟩
private def topGroup : Syntax.Expr := ⟨span 85, .group argument⟩
private def returnedLambda : Syntax.Expr := ⟨span 86,.lambda (span 87)
  ⟨span 88,[⟨span 88,.inferred ⟨span 88,"y"⟩⟩]⟩ none ⟨span 89,[⟨span 90,.returnStmt (some (ref 91 "y"))⟩]⟩⟩
private def returnArgument : Syntax.Expr := ⟨span 92,.lambda (span 93)
  ⟨span 94,[⟨span 94,.inferred ⟨span 94,"x"⟩⟩]⟩ none ⟨span 95,[⟨span 96,.returnStmt (some returnedLambda)⟩]⟩⟩
private def returnBoundary := groupedCall 97 (ref 98 "apply") returnArgument
private def inferredLetArgument : Syntax.Expr := ⟨span 101,.lambda (span 102)
  ⟨span 103,[⟨span 103,.inferred ⟨span 103,"x"⟩⟩]⟩ none ⟨span 104,
    [⟨span 105,.letDecl ⟨span 106,"y"⟩ none (some returnedLambda)⟩,⟨span 107,.returnStmt (some (ref 108 "x"))⟩]⟩⟩
private def inferredLetBoundary := groupedCall 109 (ref 110 "apply") inferredLetArgument
private theorem groupedRejected (source : Syntax.Expr) (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true)
    (child : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source = none) : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none :=
  (elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped boundary).trans child
private theorem existingRejected (source : Syntax.Expr) (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false)
    (child : elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none) : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none :=
  (elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing boundary).trans child
private theorem returnAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs returnArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | expression e => cases e with | pure r _ _ => cases r
private theorem letAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs inferredLetArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | inferred e _ => cases e with | pure r _ _ => cases r
private theorem badHeaderChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 34)
  simp only [badHeader, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument
  rfl
private theorem badBodyChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 43)
  simp only [badBody, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBodyArgument
    functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?
  rfl
private theorem nonFunctionChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration 47)
  simp only [nonFunction, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
private theorem returnChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs returnBoundary = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 98)
  have x := (elaborateExpectedComputationLambda?_eq_none_iff
    (@elaborateRecursiveLocalComputation?_iff)).mpr returnAbsent
  simp only [returnBoundary, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some, x, Option.bind_none]
private theorem letChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs inferredLetBoundary = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 110)
  have x := (elaborateExpectedComputationLambda?_eq_none_iff
    (@elaborateRecursiveLocalComputation?_iff)).mpr letAbsent
  simp only [inferredLetBoundary, groupedCall,
    elaborateGroupedExpectedLambdaArgumentApplication?, c, bind, Option.bind_some,
    x, Option.bind_none]
private theorem malformedDirectOld :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs malformedDirect = none := by
  change (if isDirectExpectedLambdaArgumentApplication malformedDirect then
    elaborateExpectedLambdaArgumentApplication? types owner inputs malformedDirect else
    elaborateRecursiveLocalComputation? inputs.names inputs.context malformedDirect) = none
  rw [show isDirectExpectedLambdaArgumentApplication malformedDirect = true by rfl]
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 51)
  simp only [malformedDirect, elaborateExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument
  rfl
private theorem oldFalseRejected (source : Syntax.Expr)
    (shape : elaborateLocalApplicationWithExpectedLambda? types owner inputs source =
      if isDirectExpectedLambdaArgumentApplication source then elaborateExpectedLambdaArgumentApplication? types owner inputs source else elaborateRecursiveLocalComputation? inputs.names inputs.context source)
    (boundary : isDirectExpectedLambdaArgumentApplication source = false)
    (child : elaborateRecursiveLocalComputation? inputs.names inputs.context source = none) :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none :=
  shape.trans (by rw [boundary]; exact child)
private theorem falseBoundaryOld : elaborateLocalApplicationWithExpectedLambda? types owner inputs doubleGroup = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs nestedSource = none ∧ elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedTuple = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedConditional = none ∧ elaborateLocalApplicationWithExpectedLambda? types owner inputs callInsideGroup = none := by
  have h : elaborateRecursiveLocalComputation? inputs.names inputs.context doubleGroup = none ∧ elaborateRecursiveLocalComputation? inputs.names inputs.context nestedSource = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context groupedTuple = none ∧ elaborateRecursiveLocalComputation? inputs.names inputs.context groupedConditional = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context callInsideGroup = none := by
    simp [doubleGroup,nestedSource,groupedTuple,groupedConditional,callInsideGroup,groupedCall,
      innerCall,argument,ordinaryArgument,ref,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]
  rcases h with ⟨d,n,t,c,i⟩
  exact ⟨oldFalseRejected doubleGroup rfl rfl d,oldFalseRejected nestedSource rfl rfl n,
    oldFalseRejected groupedTuple rfl rfl t,oldFalseRejected groupedConditional rfl rfl c,
    oldFalseRejected callInsideGroup rfl rfl i⟩
theorem selected_failures_and_shape_boundaries_are_exact :
    isOneLevelGroupedExpectedLambdaArgumentApplication badHeader = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badHeader = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badHeader = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication badBody = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badBody = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badBody = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication nonFunction = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nonFunction = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nonFunction = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication malformedDirect = false ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs malformedDirect =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs malformedDirect ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs malformedDirect = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs doubleGroup = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nestedSource = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedTuple = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedConditional = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs callInsideGroup = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs zeroArguments = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs multipleArguments = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs topGroup = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs returnBoundary = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs inferredLetBoundary = none ∧
    ¬ ∃ c t, LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs badHeader c t := by
  rcases falseBoundaryOld with ⟨d, n, t, c, i⟩
  have bh := groupedRejected badHeader rfl badHeaderChild; have bd := groupedRejected badBody rfl badBodyChild
  have nf := groupedRejected nonFunction rfl nonFunctionChild; have md := existingRejected malformedDirect rfl malformedDirectOld
  have dg := existingRejected doubleGroup rfl d; have ne := existingRejected nestedSource rfl n
  have tu := existingRejected groupedTuple rfl t; have co := existingRejected groupedConditional rfl c
  have ci := existingRejected callInsideGroup rfl i; have rb := groupedRejected returnBoundary rfl returnChild
  have lb := groupedRejected inferredLetBoundary rfl letChild
  exact ⟨rfl, badHeaderChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, bh,
    rfl, badBodyChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, bd,
    rfl, nonFunctionChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, nf, rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl, md,
    dg, ne, tu, co, ci, rfl, rfl, rfl, rb, lb,
    elaborateLocalApplicationWithGroupedExpectedLambda?_eq_none_iff.mp bh⟩
end Tests.ADR0320SymbolicLocalApplicationWithGroupedExpectedLambdaConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithOneLevelGroupedConditionalExpectedLambdaProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaProperties
/-! Independent symbolic consumer for the ADR-0338-first ADR-0337 wrapper. -/
set_option autoImplicit false
namespace Tests.ADR0339SevenLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"SevenGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 339
private def foreignOwner := declaration 9339
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
private def file : Syntax.SourceId := ⟨.main, "adr0339-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6, n + 7, n + 8, n + 9, n + 10, n + 11] callee condition yes no
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
private theorem lambdaE (n : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambda n name) lambdaCore functionType := by apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩) <;> first | exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted | exact .word | exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem applyC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") = some (.var 0, .function functionType .word) := elaborateRecursiveLocalComputation?_iff.mpr (applyE n)
private theorem flagC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "flag") = some (.var 3, .bool) := elaborateRecursiveLocalComputation?_iff.mpr (flagE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, show LocalNameTable.lookup? inputs.names "missing" = none by rfl]
private def cLO := selected 0 (lambda 10 "x") (ref 30 "ordinary")
private def cOL := selected 40 (ref 70 "ordinary") (lambda 80 "y")
private def cLL := selected 90 (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan terminalGroupSpan seventhGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨terminalGroupSpan, .group ⟨seventhGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ((isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = none
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group innermost => cases innermost with | group final => cases final with | group terminal => cases terminal with | group seventh => cases seventh
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by intro ns; induction ns with | nil => intro _ _ spine; cases spine | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem oldConditionalNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]
  simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl
  all_goals apply oldConditionalNone _ _ _ _ rfl rfl (noFiniteAt _ _ _ _) rfl rfl rfl <;> simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem newContract {s c} (e : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : NewContract s c := by
  have six : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have two : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) two
  have current := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) three
  have latest := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  have complete := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) five
  have wrapper := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) six
  let wrapped : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .sevenLevelGroupedConditional e.classified e
  refine ⟨e.classified, six, five, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional e.classified, elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, wrapped.core_hasType, ⟨wrapped.provenance, e.provenance⟩, wrapper, wrapper.trans (complete.trans (latest.trans (current.trans (previous.trans oldNone))))⟩
/-! The seven-group selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_seven_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact newContract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact newContract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))
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
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member; have route := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) h.1
  exact ⟨h.1, h.2, route, route.trans h.2⟩
private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private def threeGroupControl := selectedAt 720 [725, 726, 727] (lambda 730 "x") (ref 750 "ordinary")
private def fourGroupControl := selectedAt 750 [755, 756, 757, 758] (lambda 760 "x") (ref 780 "ordinary")
private def fiveGroupControl := selectedAt 1300 [1305, 1306, 1307, 1308, 1309] (lambda 1320 "x") (ref 1340 "ordinary")
private def sixGroupControl := selectedAt 1360 [1365, 1366, 1367, 1368, 1369, 1370] (lambda 1380 "x") (ref 1400 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
private theorem threeGroupE : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs threeGroupControl coreLO .word := .application rfl (applyE 721) (flagE 722) (.expected rfl (lambdaE 730 "x")) (.ordinary rfl (ordinaryE 750))
private theorem fourGroupE : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fourGroupControl coreLO .word := .application rfl (applyE 751) (flagE 752) (.expected rfl (lambdaE 760 "x")) (.ordinary rfl (ordinaryE 780))
private theorem fiveGroupE : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fiveGroupControl coreLO .word := .application rfl (applyE 1301) (flagE 1302) (.expected rfl (lambdaE 1320 "x")) (.ordinary rfl (ordinaryE 1340))
private theorem sixGroupE : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs sixGroupControl coreLO .word := .application rfl (applyE 1361) (flagE 1362) (.expected rfl (lambdaE 1380 "x")) (.ordinary rfl (ordinaryE 1400))
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
private theorem lambda4E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := .application (spineFrom .lambda [743, 744, 745, 746]) (applyE 741) (lambdaE 760 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda5E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := .application (spineFrom .lambda [773, 774, 775, 776, 777]) (applyE 771) (lambdaE 790 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda6E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := .application (spineFrom .lambda [798, 799, 800, 801, 802, 803]) (applyE 796) (lambdaE 815 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda7E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834]) expectedCore .word := .application (spineFrom .lambda [828, 829, 830, 831, 832, 833, 834]) (applyE 826) (lambdaE 845 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda8E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 855 [858, 859, 860, 861, 862, 863, 864, 865]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 855 [858, 859, 860, 861, 862, 863, 864, 865]) expectedCore .word := .application (spineFrom .lambda [858, 859, 860, 861, 862, 863, 864, 865]) (applyE 856) (lambdaE 875 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing five (.existing four (.existing three e)))
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e) three four five
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing five).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing four).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans ((elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old)))
private theorem currentThreeCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs threeGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.existing rfl (.threeLevelGroupedConditional threeGroupE.classified threeGroupE)))
private theorem currentFourCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fourGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.fourLevelGroupedConditional fourGroupE.classified fourGroupE))
private theorem currentFiveCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fiveGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional fiveGroupE.classified fiveGroupE)
private theorem currentSixCheck : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs sixGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr (.sixLevelGroupedConditional sixGroupE.classified sixGroupE)
private theorem completeFallback {source result} (exact : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (six : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = result := (elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing six).trans exact
private def eightGroupConditional := selectedAt 760 [765, 766, 767, 768, 769, 770, 771, 772] (lambda 780 "x") (ref 800 "ordinary")
private def allOrdinarySource := selectedAt 810 [815, 816, 817, 818, 819, 820, 821] (ref 830 "ordinary") (ref 840 "ordinary")
private def groupedOnlySource := selectedAt 890 [895, 896, 897, 898, 899, 900, 901] (groups [902] (lambda 910 "x")) (ref 930 "ordinary")
private def nestedOnlySource := selectedAt 940 [945, 946, 947, 948, 949, 950, 951] (nestedLambdaCall 952) (ref 970 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 810 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 811) (.group (.group (.group (.group (.group (.group (.group (.conditional (flagE 812) (ordinaryE 830) (ordinaryE 840)))))))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private theorem eightGroupCurrentNone : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs eightGroupConditional = none := completeFallback (currentOldNone rfl (by simpa only [eightGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768, 769, 770, 771, 772] (lambda 780 "x") (ref 800 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
private theorem groupedCurrentNone : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs groupedOnlySource = none := completeFallback (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 890 [895, 896, 897, 898, 899, 900, 901] (groups [902] (lambda 910 "x")) (ref 930 "ordinary") rfl rfl (noFiniteAt 890 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
private theorem nestedCurrentNone : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs nestedOnlySource = none := completeFallback (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 940 [945, 946, 947, 948, 949, 950, 951] (nestedLambdaCall 952) (ref 970 "ordinary") rfl rfl (noFiniteAt 940 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (sixGroupControl, some (coreLO, .word)), (eightGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834], some (expectedCore, .word)), (lambdaApplication 855 [858, 859, 860, 861, 862, 863, 864, 865], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type)) ∧ ((isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); let wrapped : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child; exact ⟨wrapped, child, wrapped.provenance, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl immediateE) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl oneGroupE rfl)) | exact completeOption (completeFallback (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))) | exact completeOption (completeFallback currentThreeCheck) | exact completeOption (completeFallback currentFourCheck) | exact completeOption (completeFallback currentFiveCheck) | exact completeOption currentSixCheck | exact completeOption eightGroupCurrentNone | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl)) | exact completeOption groupedCurrentNone | exact completeOption nestedCurrentNone | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda0E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda1E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda2E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda3E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda4E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda5E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda6E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda7E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda8E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl)) | exact completeOption (completeFallback rfl)
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (sixGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834], some (expectedCore, .word)), (lambdaApplication 855 [858, 859, 860, 861, 862, 863, 864, 865], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr (.sevenLevelGroupedConditional eLO.classified eLO) | exact elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr (.sevenLevelGroupedConditional eOL.classified eOL) | exact elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr (.sevenLevelGroupedConditional eLL.classified eLL) | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousSixConditionalCurrentNone : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1440 [1445, 1446, 1447, 1448, 1449, 1450] (badHeader 1460) (ref 1470 "ordinary")) = none := by rw [elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional (by rfl)]; simp [elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousFiveConditionalCurrentNone : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 980 [985, 986, 987, 988, 989] (badHeader 990) (ref 1000 "ordinary")) = none := by rw [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional (by rfl)]; simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousFourConditionalCurrentNone : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary")) = none := by rw [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional (by rfl)]; simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousThreeConditionalCurrentNone : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary")) = none := by rw [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (by rfl)]; simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousTwoConditionalCurrentNone : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary")) = none := by rw [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional (by rfl)]; simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
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
private def inheritedAndBoundaryFailures := [selectedAt 1440 [1445, 1446, 1447, 1448, 1449, 1450] (badHeader 1460) (ref 1470 "ordinary"), selectedAt 980 [985, 986, 987, 988, 989] (badHeader 990) (ref 1000 "ordinary"), selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary"), selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary"), selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary"), selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private def InheritedFailure (source : Syntax.Expr) : Prop := isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := by have route := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary; exact ⟨boundary, rejected, current, route, route.trans current⟩
private theorem inheritOld {source : Syntax.Expr} (current : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (six : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := inherit (completeFallback current six) boundary rejected
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousSixConditionalCurrentNone
  · exact inheritOld previousFiveConditionalCurrentNone
  · exact inheritOld ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousFourConditionalCurrentNone)
  · exact inheritOld ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousThreeConditionalCurrentNone))
  · exact inheritOld ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone)))
  all_goals first | exact inheritOld (currentOldNone rfl previousOneConditionalNone) | exact inheritOld (currentOldNone rfl previousImmediateConditionalNone) | exact inheritOld (currentOldNone rfl previousThreeGroupLambdaNone) | exact inheritOld (currentOldNone rfl previousTwoGroupLambdaNone) | exact inheritOld (currentOldNone rfl previousOneGroupLambdaNone) | exact inheritOld (currentOldNone rfl previousDirectLambdaNone) | exact inheritOld (currentOldNone rfl tuplePreviousNone) | exact inheritOld (currentOldNone rfl nestedPreviousNone) | exact inheritOld (currentOldNone rfl returnPreviousNone) | exact inheritOld (currentOldNone rfl letPreviousNone)
/-! Selected failures are final; every false neighbor retains the complete ADR-0337 Option. -/
theorem selected_failures_and_complete_adr0337_options_are_exact :
    (∀ source ∈ selectedFailures, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing⟩
end Tests.ADR0339SevenLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithSixLevelGroupedConditionalExpectedLambdaProperties
/-! Independent symbolic consumer for the ADR-0336-first ADR-0335 wrapper. -/
set_option autoImplicit false
namespace Tests.ADR0337SixLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"SixGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 337
private def foreignOwner := declaration 9337
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
private def file : Syntax.SourceId := ⟨.main, "adr0337-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6, n + 7, n + 8, n + 9, n + 10] callee condition yes no
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
private theorem lambdaE (n : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambda n name) lambdaCore functionType := by apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩) <;> first | exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted | exact .word | exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem applyC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") = some (.var 0, .function functionType .word) := elaborateRecursiveLocalComputation?_iff.mpr (applyE n)
private theorem flagC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "flag") = some (.var 3, .bool) := elaborateRecursiveLocalComputation?_iff.mpr (flagE n)
private theorem wrongC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, show LocalNameTable.lookup? inputs.names "missing" = none by rfl]
private def cLO := selected 0 (lambda 10 "x") (ref 30 "ordinary")
private def cOL := selected 40 (ref 70 "ordinary") (lambda 80 "y")
private def cLL := selected 90 (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan terminalGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨terminalGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ((isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = none
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group innermost => cases innermost with | group terminal => cases terminal with | group final => cases final
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by intro ns; induction ns with | nil => intro _ _ spine; cases spine | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem oldConditionalNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]
  simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl
  all_goals apply oldConditionalNone _ _ _ _ rfl rfl (noFiniteAt _ _ _ _) rfl rfl rfl <;> simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem newContract {s c} (e : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : NewContract s c := by
  have five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have two : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) two
  have current := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) three
  have older := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  have latest := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) five
  let wrapped : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .sixLevelGroupedConditional e.classified e
  refine ⟨e.classified, five, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional e.classified, elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, wrapped.core_hasType, ⟨wrapped.provenance, e.provenance⟩, latest, latest.trans (older.trans (current.trans (previous.trans oldNone)))⟩
/-! The six-group selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_six_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact newContract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact newContract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))
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
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member; have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) h.1
  exact ⟨h.1, h.2, route, route.trans h.2⟩
private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private def threeGroupControl := selectedAt 720 [725, 726, 727] (lambda 730 "x") (ref 750 "ordinary")
private def fourGroupControl := selectedAt 750 [755, 756, 757, 758] (lambda 760 "x") (ref 780 "ordinary")
private def fiveGroupControl := selectedAt 785 [790, 791, 792, 793, 794] (lambda 805 "x") (ref 825 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
private theorem threeGroupE : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs threeGroupControl coreLO .word := .application rfl (applyE 721) (flagE 722) (.expected rfl (lambdaE 730 "x")) (.ordinary rfl (ordinaryE 750))
private theorem fourGroupE : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fourGroupControl coreLO .word := .application rfl (applyE 751) (flagE 752) (.expected rfl (lambdaE 760 "x")) (.ordinary rfl (ordinaryE 780))
private theorem fiveGroupE : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fiveGroupControl coreLO .word := .application rfl (applyE 786) (flagE 787) (.expected rfl (lambdaE 805 "x")) (.ordinary rfl (ordinaryE 825))
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
private theorem lambda4E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := .application (spineFrom .lambda [743, 744, 745, 746]) (applyE 741) (lambdaE 760 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda5E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 770 [773, 774, 775, 776, 777]) expectedCore .word := .application (spineFrom .lambda [773, 774, 775, 776, 777]) (applyE 771) (lambdaE 790 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda6E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 795 [798, 799, 800, 801, 802, 803]) expectedCore .word := .application (spineFrom .lambda [798, 799, 800, 801, 802, 803]) (applyE 796) (lambdaE 815 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem lambda7E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 835 [838, 839, 840, 841, 842, 843, 844]) expectedCore .word := by let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 835 [838, 839, 840, 841, 842, 843, 844]) expectedCore .word := .application (spineFrom .lambda [838, 839, 840, 841, 842, 843, 844]) (applyE 836) (lambdaE 855 "x"); exact .threeOrMoreGrouped rfl child.classified child
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing five (.existing four (.existing three e)))
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e) three four five
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing five).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing four).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans ((elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old)))
private theorem currentThreeCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs threeGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.existing rfl (.threeLevelGroupedConditional threeGroupE.classified threeGroupE)))
private theorem currentFourCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fourGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.fourLevelGroupedConditional fourGroupE.classified fourGroupE))
private theorem currentFiveCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fiveGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional fiveGroupE.classified fiveGroupE)
private def sevenGroupConditional := selectedAt 760 [765, 766, 767, 768, 769, 770, 771] (lambda 780 "x") (ref 800 "ordinary")
private def allOrdinarySource := selectedAt 810 [815, 816, 817, 818, 819, 820] (ref 825 "ordinary") (ref 830 "ordinary")
private def groupedOnlySource := selectedAt 840 [845, 846, 847, 848, 849, 850] (groups [851] (lambda 860 "x")) (ref 880 "ordinary")
private def nestedOnlySource := selectedAt 890 [895, 896, 897, 898, 899, 900] (nestedLambdaCall 905) (ref 920 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 810 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 811) (.group (.group (.group (.group (.group (.group (.conditional (flagE 812) (ordinaryE 825) (ordinaryE 830))))))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (sevenGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 835 [838, 839, 840, 841, 842, 843, 844], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type)) ∧ ((isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); let wrapped : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child; exact ⟨wrapped, child, wrapped.provenance, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (currentOldCheck rfl (.existing rfl immediateE) rfl)
  · exact completeOption (currentOldCheck rfl oneGroupE rfl)
  · exact completeOption (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))
  · exact completeOption currentThreeCheck
  · exact completeOption currentFourCheck
  · exact completeOption currentFiveCheck
  · exact completeOption (currentOldNone rfl (by simpa only [sevenGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768, 769, 770, 771] (lambda 780 "x") (ref 800 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl)
  · exact completeOption (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 840 [845, 846, 847, 848, 849, 850] (groups [851] (lambda 860 "x")) (ref 880 "ordinary") rfl rfl (noFiniteAt 840 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 890 [895, 896, 897, 898, 899, 900] (nestedLambdaCall 905) (ref 920 "ordinary") rfl rfl (noFiniteAt 890 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda0E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda1E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda2E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda3E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda4E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda5E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda6E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda7E) rfl)
  · exact completeOption (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl)
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 835 [838, 839, 840, 841, 842, 843, 844], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr (.sixLevelGroupedConditional eLO.classified eLO) | exact elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr (.sixLevelGroupedConditional eOL.classified eOL) | exact elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr (.sixLevelGroupedConditional eLL.classified eLL) | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousFiveConditionalCurrentNone : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 980 [985, 986, 987, 988, 989] (badHeader 990) (ref 1000 "ordinary")) = none := by rw [elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional (by rfl)]; simp [elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousFourConditionalCurrentNone : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary")) = none := by rw [elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional (by rfl)]; simp [elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousThreeConditionalCurrentNone : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary")) = none := by rw [elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (by rfl)]; simp [elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
private theorem previousTwoConditionalCurrentNone : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary")) = none := by rw [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional (by rfl)]; simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
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
private def inheritedAndBoundaryFailures := [selectedAt 980 [985, 986, 987, 988, 989] (badHeader 990) (ref 1000 "ordinary"), selectedAt 1010 [1015, 1016, 1017, 1018] (badHeader 1020) (ref 1030 "ordinary"), selectedAt 1040 [1045, 1046, 1047] (badHeader 1050) (ref 1060 "ordinary"), selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary"), selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private def InheritedFailure (source : Syntax.Expr) : Prop := isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := by have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary; exact ⟨boundary, rejected, current, route, route.trans current⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousFiveConditionalCurrentNone
  · exact inherit ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousFourConditionalCurrentNone)
  · exact inherit ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousThreeConditionalCurrentNone))
  · exact inherit ((elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone)))
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)
/-! Selected failures are final; every false neighbor retains the complete ADR-0335 Option. -/
theorem selected_failures_and_complete_adr0335_options_are_exact :
    (∀ source ∈ selectedFailures, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing⟩
end Tests.ADR0337SixLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaProperties
/-! Independent symbolic consumer for the ADR-0330-first ADR-0329 wrapper. -/
set_option autoImplicit false

namespace Tests.ADR0331ThreeLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ThreeGroupedConditionalFirst", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 331
private def foreignOwner := declaration 9331
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
private def file : Syntax.SourceId := ⟨.main, "adr0331-symbolic.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (ns : List Nat) (e : Syntax.Expr) : Syntax.Expr := ns.foldr (fun n inner => ⟨span n, .group inner⟩) e
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def atGroups (n : Nat) (ns : List Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (groups ns (conditional n condition yes no))
private def candidate (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := atGroups n [n + 5, n + 6, n + 7] callee condition yes no
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
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NestedProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  ((isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) ∨ (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word)) ∧ ChildProvenance s c
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = some (c, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ Core.HasType inputs.context.values c .word ∧ NestedProvenance s c
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild with | group final => cases final
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by intro ns; induction ns with | nil => intro _ _ spine; cases spine | cons head tail ih => intro _ _ spine; change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine; cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by apply Bool.eq_false_iff.mpr; intro old; obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old; exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem oldConditionalNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false) (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two, elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped]
  simp only [selectedAt, atGroups, call] at direct inferred ⊢; simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl
  all_goals apply oldConditionalNone _ _ _ _ rfl rfl (noFiniteAt _ _ _ _) rfl rfl rfl <;> simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private theorem newContract {s c} (e : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : NewContract s c := by
  have oldBoundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false := by cases e; rfl
  have current := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) oldBoundary
  let wrapped : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs s c .word := .threeLevelGroupedConditional e.classified e
  refine ⟨e.classified, oldBoundary, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, wrapped, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional e.classified, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, current, current.trans oldNone, wrapped.core_hasType, ?_⟩
  exact ⟨wrapped.provenance, e.provenance⟩

/-! The three selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_three_level_grouped_conditional_routes_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ NewContract cLO coreLO ∧ NewContract cOL coreOL ∧ NewContract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact newContract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact newContract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact newContract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))

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
private theorem selectedFailuresChild : ∀ source ∈ selectedFailures, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by
  intro source member; simp only [selectedFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, wrongC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, missingC]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badHeaderNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, badBodyNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, wrongNone]⟩
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, missingBranchNone]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, flagC]⟩
  · exact ⟨rfl, by simp [candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, missingC]⟩
  · refine ⟨rfl, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩
    rintro ⟨_, _, e⟩; cases e with | application _ callee _ _ no =>
      have c := elaborateRecursiveLocalComputation?_iff.mpr callee; rw [applyC] at c; cases c
      have rejected := elaborateConditionalExpectedLambdaBranch?_iff.mpr no; rw [groupedLambdaNone] at rejected; cases rejected
  · exact ⟨rfl, by simp [selected, candidate, atGroups, groups, conditional, call, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?, applyC, flagC, nestedLambdaCallNone]⟩
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional h.1, (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional h.1).trans h.2⟩

private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
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
private theorem lambda4E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 740 [743, 744, 745, 746]) expectedCore .word := .application (spineFrom .lambda [743, 744, 745, 746]) (applyE 741) (lambdaE 760 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr e
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e)
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old
private def fourGroupConditional := selectedAt 760 [765, 766, 767, 768] (lambda 770 "x") (ref 790 "ordinary")
private def allOrdinarySource := selectedAt 800 [805, 806, 807] (ref 810 "ordinary") (ref 820 "ordinary")
private def groupedOnlySource := selectedAt 830 [835, 836, 837] (groups [840] (lambda 850 "x")) (ref 870 "ordinary")
private def nestedOnlySource := selectedAt 880 [885, 886, 887] (nestedLambdaCall 890) (ref 910 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 800 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 801) (.group (.group (.group (.conditional (flagE 802) (ordinaryE 810) (ordinaryE 820)))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (fourGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type)) ∧ ((isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) boundary
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed)
  let wrapped : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core type := .existing boundary child
  exact ⟨child, wrapped, wrapped.provenance, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (currentOldCheck rfl (.existing rfl immediateE))
  · exact completeOption (currentOldCheck rfl oneGroupE)
  · exact completeOption (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))
  · exact completeOption (currentOldNone rfl (by simpa only [fourGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768] (lambda 770 "x") (ref 790 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl allOrdinaryE))
  · exact completeOption (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 830 [835, 836, 837] (groups [840] (lambda 850 "x")) (ref 870 "ordinary") rfl rfl (noFiniteAt 830 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 880 [885, 886, 887] (nestedLambdaCall 890) (ref 910 "ordinary") rfl rfl (noFiniteAt 880 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda0E))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda1E))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda2E))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda3E))
  · exact completeOption (currentOldCheck rfl (.existing rfl lambda4E))
  · exact completeOption (currentOldCheck rfl (.existing rfl ordinaryApplicationE))
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl

private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word))]
private theorem neighborCheck {item} (member : item ∈ completeNeighbors) : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := (completeOptionsExact item member).2.2.2.2.1
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr (.threeLevelGroupedConditional eLO.classified eLO) | exact elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr (.threeLevelGroupedConditional eOL.classified eOL) | exact elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr (.threeLevelGroupedConditional eLL.classified eLL) | exact neighborCheck (by simp [completeNeighbors])

/-! Child Cores stay literal; manual, runner-sound and deterministic execution agree. -/
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2) ∧
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨runtimeSelectionsExact, conditionalRuns, lambdaRuns, ?_, ?_⟩
  · intro choice core member; exact ⟨conditionalFuels choice core member, conditionalRunnerSound choice core member, conditionalDeterministic choice core member⟩
  · intro choice core member; exact ⟨lambdaFuels choice core member, lambdaRunnerSound choice core member, lambdaDeterministic choice core member⟩
private def returnArgument : Syntax.Expr := ⟨span 1600, .lambda (span 1601) ⟨span 1602, [⟨span 1602, .inferred ⟨span 1602, "x"⟩⟩]⟩ none ⟨span 1603, [⟨span 1604, .returnStmt (some (lambda 1610 "y"))⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 1620, .lambda (span 1621) ⟨span 1622, [⟨span 1622, .inferred ⟨span 1622, "x"⟩⟩]⟩ none ⟨span 1623, [⟨span 1624, .letDecl ⟨span 1625, "y"⟩ none (some (lambda 1630 "z"))⟩, ⟨span 1626, .returnStmt (some (ref 1627 "x"))⟩]⟩⟩
private theorem previousTwoConditionalCurrentNone : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary")) = none := by rw [elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional (by rfl)]; simp [elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?, selectedAt, atGroups, groups, conditional, call, applyC, flagC, badHeaderNone]
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
private def inheritedAndBoundaryFailures := [selectedAt 1070 [1075, 1076] (badHeader 1080) (ref 1090 "ordinary"), selectedAt 1100 [1105] (badHeader 1110) (ref 1120 "ordinary"), selectedAt 1130 [] (badHeader 1140) (ref 1150 "ordinary"), call 1160 (ref 1161 "apply") (groups [1163, 1164, 1165] (badHeader 1170)), call 1180 (ref 1181 "apply") (groups [1183, 1184] (badHeader 1190)), call 1200 (ref 1201 "apply") (groups [1203] (badHeader 1210)), call 1220 (ref 1221 "apply") (badHeader 1230), call 1240 (ref 1241 "apply") ⟨span 1242, .tuple ⟨span 1243, [lambda 1250 "x", ref 1260 "ordinary"]⟩⟩, call 1270 (ref 1271 "ordinary") (call 1272 (ref 1273 "apply") (lambda 1274 "x")), call 1280 (ref 1281 "apply") returnArgument, call 1290 (ref 1291 "apply") letArgument]
private def InheritedFailure (source : Syntax.Expr) : Prop := isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing boundary, (elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans current⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousTwoConditionalCurrentNone
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)

/-! Selected failures are final; every false neighbor retains the complete ADR-0329 Option. -/
theorem selected_failures_and_complete_adr0329_options_are_exact :
    (∀ source ∈ selectedFailures, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, fun _ _ _ _ => elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing⟩

end Tests.ADR0331ThreeLevelGroupedConditionalFirstWrapperSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationWithTwoLevelGroupedExpectedLambdaProperties
/-! Independent symbolic consumer for the exact-two-first ADR-0322 entry. -/
set_option autoImplicit false
namespace Tests.ADR0322SymbolicLocalApplicationWithTwoLevelGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main,
  ⟨[⟨"TwoLevelGroupFirst", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 322
private def foreignOwner := declaration 9322
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell (.function .word .unit)⟩, ⟨"apply", duplicateId, .unit⟩, ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "two-level-group-first.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (positions : List Nat) (source : Syntax.Expr) : Syntax.Expr := positions.foldr (fun n inner => ⟨span n, .group inner⟩) source
private def callAt (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def twoCall (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := callAt n callee ⟨span (n + 2), .group ⟨span (n + 3), .group argument⟩⟩
private def body : Syntax.Block := ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr := ⟨span 4, .lambda (span 5)
  ⟨span 6, [⟨span 6, .inferred ⟨span 6, "x"⟩⟩]⟩ none body⟩
private def directSource := callAt 20 (ref 22 "apply") argument
private def oneGroupSource := callAt 23 (ref 25 "apply") (groups [26] argument)
private def twoGroupSource := twoCall 0 (ref 10 "apply") argument
private def threeGroupSource := twoCall 27 (ref 31 "apply") (groups [32] argument)
private def expectedCore : Core.Expr := .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private def ordinaryArgument := ref 40 "ordinary"
private def ordinarySource (n : Nat) (positions : List Nat) := callAt n (ref (n + 4) "apply") (groups positions ordinaryArgument)
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem groupedOrdinaryElaboration (positions : List Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (groups positions ordinaryArgument) (.var 4) functionType := by
  induction positions with
  | nil => exact ordinaryElaboration 40
  | cons _ _ ih => exact .group ih
private theorem lambdaElaboration : ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs argument (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner "x" .word, body, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem directEvidence : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs directSource expectedCore .word :=
  .existing rfl (.existing rfl (.expected rfl (.application (applyElaboration 22) lambdaElaboration)))
private theorem oneGroupEvidence : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs oneGroupSource expectedCore .word :=
  .existing rfl (.grouped rfl (.application (applyElaboration 25) lambdaElaboration))
private theorem twoGroupEvidence : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs twoGroupSource expectedCore .word :=
  .twoLevel rfl (.application (applyElaboration 10) lambdaElaboration)
private theorem ordinaryEvidence (n : Nat) (positions : List Nat)
    (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (ordinarySource n positions) = false)
    (one : isOneLevelGroupedExpectedLambdaArgumentApplication (ordinarySource n positions) = false)
    (direct : isDirectExpectedLambdaArgumentApplication (ordinarySource n positions) = false) :
    LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (ordinarySource n positions) ordinaryCore .word :=
  .existing two (.existing one (.ordinary direct (.application (applyElaboration (n + 4)) (groupedOrdinaryElaboration positions))))
private theorem expectedPaths : ∀ source ∈ [directSource, oneGroupSource],
    isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = some (expectedCore, .word) := by
  intro source membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with h | h <;> subst source
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr directEvidence⟩
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr oneGroupEvidence⟩
private theorem ordinaryPaths : ∀ source ∈ [ordinarySource 50 [], ordinarySource 53 [55], ordinarySource 56 [58, 59], ordinarySource 60 [62, 63, 64]],
    isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = some (ordinaryCore, .word) := by
  intro source membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with h | h | h | h <;> subst source
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (ordinaryEvidence 50 [] rfl rfl rfl)⟩
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (ordinaryEvidence 53 [55] rfl rfl rfl)⟩
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (ordinaryEvidence 56 [58, 59] rfl rfl rfl)⟩
  · exact ⟨rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing rfl, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (ordinaryEvidence 60 [62, 63, 64] rfl rfl rfl)⟩
private theorem twoProvenance : isTwoLevelGroupedExpectedLambdaArgumentApplication twoGroupSource = true ∧
    TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupSource expectedCore .word := by
  rcases twoGroupEvidence.provenance with h | h
  · exact h
  · cases h.1
/-- The new branch and every frozen successful branch retain exact semantics. -/
theorem all_preserved_and_two_level_paths_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    (∀ source ∈ [directSource, oneGroupSource],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = some (expectedCore, .word)) ∧
    isTwoLevelGroupedExpectedLambdaArgumentApplication twoGroupSource = true ∧
    LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs twoGroupSource expectedCore .word ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs twoGroupSource =
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs twoGroupSource ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs twoGroupSource = some (expectedCore, .word) ∧
    Core.HasType inputs.context.values expectedCore .word ∧
    (isTwoLevelGroupedExpectedLambdaArgumentApplication twoGroupSource = true ∧
      TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupSource expectedCore .word) ∧
    (∀ source ∈ [ordinarySource 50 [], ordinarySource 53 [55],
        ordinarySource 56 [58, 59], ordinarySource 60 [62, 63, 64]],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = some (ordinaryCore, .word)) ∧
    Core.HasType inputs.context.values ordinaryCore .word := by
  change (["apply", "opaque", "apply", "flag", "ordinary"].zip [applyId, opaqueId, duplicateId, flagId, ordinaryId])[1]?.map Prod.snd = some opaqueId ∧ _
  exact ⟨rfl, rfl, expectedPaths, rfl, twoGroupEvidence,
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel rfl,
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr twoGroupEvidence,
    twoGroupEvidence.core_hasType, twoProvenance, ordinaryPaths,
    (ordinaryEvidence 50 [] rfl rfl rfl).core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def duplicateValue : Core.Value := .cellRef (.function .unit .word) 31
private def ordinaryValue : Core.Value := .closure .word .word (.var 0)
  [.hostFunction .storageRead]
private def applyValue : Core.Value := .closure functionType .word
  (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment : Core.Environment :=
  [applyValue, opaqueValue, duplicateValue, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The common selected Core independently executes without changing the store. -/
theorem independently_executed_selected_core :
    environment[1]? = some opaqueValue ∧ store[0]? = some opaqueValue ∧
    Core.Evaluates environment store expectedCore (.word seven) store := by
  exact ⟨rfl, rfl, .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))⟩
private def badHeaderArgument : Syntax.Expr :=
  ⟨span 70, .lambda (span 71) ⟨span 72, []⟩ none body⟩
private def badBodyArgument : Syntax.Expr := ⟨span 73, .lambda (span 74)
  ⟨span 75, [⟨span 75, .inferred ⟨span 75, "x"⟩⟩]⟩ none
  ⟨span 76, [⟨span 77, .returnStmt none⟩]⟩⟩
private def innerCall := callAt 78 (ref 80 "apply") argument
private def tupleArgument : Syntax.Expr :=
  ⟨span 81, .tuple ⟨span 82, [argument, ordinaryArgument]⟩⟩
private def conditionalArgument : Syntax.Expr := ⟨span 83,
  .conditional (ref 84 "flag") (span 85) argument (span 86) ordinaryArgument⟩
private def returnedLambda : Syntax.Expr := ⟨span 87, .lambda (span 88)
  ⟨span 89, [⟨span 89, .inferred ⟨span 89, "y"⟩⟩]⟩ none
  ⟨span 90, [⟨span 91, .returnStmt (some (ref 92 "y"))⟩]⟩⟩
private def returnArgument : Syntax.Expr := ⟨span 93, .lambda (span 94)
  ⟨span 95, [⟨span 95, .inferred ⟨span 95, "x"⟩⟩]⟩ none
  ⟨span 96, [⟨span 97, .returnStmt (some returnedLambda)⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 98, .lambda (span 99)
  ⟨span 100, [⟨span 100, .inferred ⟨span 100, "x"⟩⟩]⟩ none ⟨span 101,
  [⟨span 102, .letDecl ⟨span 103, "y"⟩ none (some returnedLambda)⟩,
   ⟨span 104, .returnStmt (some (ref 105 "x"))⟩]⟩⟩
private def badHeaderSource := twoCall 116 (ref 120 "apply") badHeaderArgument
private def badBodySource := twoCall 121 (ref 125 "apply") badBodyArgument
private def nonFunctionSource := twoCall 126 (ref 130 "flag") argument
private def unresolvedSource := twoCall 131 (ref 135 "missing") argument
private def nestedSource := callAt 136 (ref 138 "ordinary") twoGroupSource
private def tupleSource := twoCall 139 (ref 143 "apply") tupleArgument
private def conditionalSource := twoCall 144 (ref 148 "apply") conditionalArgument
private def callSource := twoCall 149 (ref 153 "apply") innerCall
private def zeroArguments : Syntax.Expr :=
  ⟨span 154, .call (ref 156 "apply") ⟨span 155, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 157, .call (ref 159 "apply")
  ⟨span 158, [groups [160, 161] argument, ordinaryArgument]⟩⟩
private def topGroups := groups [162, 163] argument
private def returnSource := twoCall 106 (ref 110 "apply") returnArgument
private def letSource := twoCall 111 (ref 115 "apply") letArgument
private theorem twoApplyRejected (n : Nat) (candidate : Syntax.Expr) (rejected :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs candidate functionType = none) :
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (twoCall n (ref (n + 4) "apply") candidate) = none := by
  have callee := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration (n + 4))
  simp only [twoCall, callAt, elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, callee, bind, Option.bind_some, rejected, Option.bind_none]
private theorem expectedAbsent (candidate : Syntax.Expr) (absent : ¬ ∃ c,
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs candidate c functionType) :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs candidate functionType = none :=
  (elaborateExpectedComputationLambda?_eq_none_iff (@elaborateRecursiveLocalComputation?_iff)).mpr absent
private theorem returnAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs returnArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | expression e => cases e with | pure r _ _ => cases r
private theorem letAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs letArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | inferred e _ => cases e with | pure r _ _ => cases r
private theorem selectedRejected (source : Syntax.Expr) (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = true)
    (child : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source = none) :
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
        elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none :=
  ⟨elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel boundary,
   (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel boundary).trans child⟩
private theorem oldRejected (source : Syntax.Expr) (shape : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source =
      if isDirectExpectedLambdaArgumentApplication source then
        elaborateExpectedLambdaArgumentApplication? types owner inputs source
      else elaborateRecursiveLocalComputation? inputs.names inputs.context source)
    (boundary : isDirectExpectedLambdaArgumentApplication source = false)
    (child : elaborateRecursiveLocalComputation? inputs.names inputs.context source = none) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none := shape.trans (by rw [boundary]; exact child)
private theorem existingRejected (source : Syntax.Expr) (boundary : isTwoLevelGroupedExpectedLambdaArgumentApplication source = false)
    (child : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none) :
    isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
      elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none :=
  ⟨boundary, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing boundary,
    (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing boundary).trans child⟩
private theorem compoundOldFailures :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs threeGroupSource = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nestedSource = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs tupleSource = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs conditionalSource = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs callSource = none := by
  have h : elaborateRecursiveLocalComputation? inputs.names inputs.context threeGroupSource = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context nestedSource = none ∧ elaborateRecursiveLocalComputation? inputs.names inputs.context tupleSource = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context conditionalSource = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context callSource = none := by
    simp [threeGroupSource, nestedSource, tupleSource, conditionalSource, callSource, twoGroupSource,
      twoCall, callAt, groups, innerCall, tupleArgument, conditionalArgument, argument,
      ordinaryArgument, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
  rcases h with ⟨d, n, t, c, i⟩
  exact ⟨oldRejected threeGroupSource rfl rfl d, oldRejected nestedSource rfl rfl n, oldRejected tupleSource rfl rfl t,
    oldRejected conditionalSource rfl rfl c, oldRejected callSource rfl rfl i⟩
private theorem selectedMembership
    (bh : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs badHeaderSource = none)
    (bb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs badBodySource = none)
    (nf : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunctionSource = none)
    (missing : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs unresolvedSource = none)
    (rb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs returnSource = none)
    (lb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs letSource = none) :
    ∀ source ∈ [badHeaderSource, badBodySource, nonFunctionSource, unresolvedSource, returnSource, letSource],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none := by
  intro source membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨rfl, selectedRejected _ rfl bh⟩ | exact ⟨rfl, selectedRejected _ rfl bb⟩
          | exact ⟨rfl, selectedRejected _ rfl nf⟩ | exact ⟨rfl, selectedRejected _ rfl missing⟩
          | exact ⟨rfl, selectedRejected _ rfl rb⟩ | exact ⟨rfl, selectedRejected _ rfl lb⟩
private theorem existingMembership (d : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs threeGroupSource = none)
    (n : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nestedSource = none)
    (t : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs tupleSource = none)
    (c : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs conditionalSource = none)
    (i : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs callSource = none) :
    ∀ source ∈ [threeGroupSource, nestedSource, tupleSource, conditionalSource, callSource, zeroArguments, multipleArguments, topGroups],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none := by
  intro source membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with h | h | h | h | h | h | h | h <;> subst source
  · exact existingRejected _ rfl d
  · exact existingRejected _ rfl n
  · exact existingRejected _ rfl t
  · exact existingRejected _ rfl c
  · exact existingRejected _ rfl i
  · exact existingRejected _ rfl rfl
  · exact existingRejected _ rfl rfl
  · exact existingRejected _ rfl rfl
/-- Recognized failure is final, while every other negative remains ADR-0320-owned. -/
theorem selected_failures_and_shape_boundaries_are_exact :
    (∀ source ∈ [badHeaderSource, badBodySource, nonFunctionSource, unresolvedSource, returnSource, letSource],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = true ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
        elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none) ∧
    (∀ source ∈ [threeGroupSource, nestedSource, tupleSource, conditionalSource, callSource, zeroArguments, multipleArguments, topGroups],
      isTwoLevelGroupedExpectedLambdaArgumentApplication source = false ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source =
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source ∧
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs source = none) ∧
    ¬ ∃ c t, LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs badHeaderSource c t := by
  have bh := twoApplyRejected 116 badHeaderArgument (by unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument; rfl)
  have bb := twoApplyRejected 121 badBodyArgument (by unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBodyArgument functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl)
  have nf : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunctionSource = none := by
    have c := elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration 130)
    simp only [nonFunctionSource, twoCall, callAt, elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, c, bind, Option.bind_some]
  have missing : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs unresolvedSource = none := by
    have c : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref 135 "missing") = none := by
      have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
      simp only [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent, Option.map_none, bind, Option.bind_none]
    simp only [unresolvedSource, twoCall, callAt, elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, c, bind, Option.bind_none]
  have rb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs returnSource = none := by simpa only [returnSource] using (twoApplyRejected 106 returnArgument (expectedAbsent returnArgument returnAbsent))
  have lb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs letSource = none := by simpa only [letSource] using (twoApplyRejected 111 letArgument (expectedAbsent letArgument letAbsent))
  have selected := selectedMembership bh bb nf missing rb lb
  rcases compoundOldFailures with ⟨d, n, t, c, i⟩
  have existing := existingMembership d n t c i
  exact ⟨selected, existing, elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_eq_none_iff.mp (selectedRejected badHeaderSource rfl bh).2⟩
end Tests.ADR0322SymbolicLocalApplicationWithTwoLevelGroupedExpectedLambdaConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda
/-! Independent parsed integration consumer for conditional-first finite-group dispatch. -/
set_option autoImplicit false
namespace Tests.ADR0325ParsedUnifiedConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda | allOrdinary | grouped
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnifiedExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 325
private def foreignOwner := declaration 9325
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5),
      .inferred ⟨range file (start + 4) (start + 5), "x"⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16),
      .returnStmt (some (reference file (start + 14) (start + 15) "x"))⟩]⟩⟩
private def conditionalSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 42, .call (reference file 0 5 "apply") ⟨range file 5 42,
    [⟨range file 6 41, .conditional (reference file 6 10 "flag") (range file 11 12)
      (lambdaAt file 13) (range file 31 32) (reference file 33 41 "ordinary")⟩]⟩⟩
private def twoGrouped (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 6 27, .group ⟨range file 7 26, .group (lambdaAt file 8)⟩⟩
private def twoSource (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 0 28, .call (reference file 0 5 "apply") ⟨range file 5 28, [twoGrouped file]⟩⟩
private def threeGrouped (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 29, .group ⟨range file 7 28, .group
    ⟨range file 8 27, .group (lambdaAt file 9)⟩⟩⟩
private def threeSource (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 0 30, .call (reference file 0 5 "apply") ⟨range file 5 30, [threeGrouped file]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def groupedCore : Core.Expr := .apply (.var 0) lambdaCore
private def conditionalCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
private theorem calleeElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 6 10 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaElaboration (file : Syntax.SourceFile) (start : Nat) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) "x"))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))
private theorem conditionalChild (file : Syntax.SourceFile) : ConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs (conditionalSource file) conditionalCore .word :=
  .application rfl (calleeElaboration file) (flagElaboration file)
    (.expected rfl (lambdaElaboration file 13)) (.ordinary rfl (ordinaryElaboration file 33 41))
private theorem threeChild (file : Syntax.SourceFile) : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
    types owner inputs (threeSource file) groupedCore .word :=
  .application (.group (.group (.group .lambda)))
    (calleeElaboration file) (lambdaElaboration file 9)
private theorem twoChild (file : Syntax.SourceFile) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs (twoSource file) groupedCore .word :=
  .twoLevel rfl (.application (calleeElaboration file) (lambdaElaboration file 8))
private theorem nonGroupBoundaries (file : Syntax.SourceFile) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (conditionalSource file) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (twoSource file) = false := by
  constructor <;> cases selected : isThreeOrMoreGroupedExpectedLambdaArgumentApplication _
  · rfl
  · rcases isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected with ⟨_, _, _, _, _, spine⟩
    cases spine
  · rfl
  · rcases isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected with ⟨_, _, _, _, _, spine⟩
    cases spine with | group child => cases child with | group child => cases child
private theorem conditionalWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (conditionalSource file) conditionalCore .word :=
  .conditional rfl (conditionalChild file)
private theorem threeWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (threeSource file) groupedCore .word :=
  .threeOrMoreGrouped rfl (threeChild file).classified (threeChild file)
private theorem twoWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word :=
  .existing rfl (nonGroupBoundaries file).2 (twoChild file)
/-! The exact routes retain child, wrapper, executable, classifier, typing and provenance. -/
theorem parsed_unified_static_contract (file : Syntax.SourceFile) :
    (ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (conditionalSource file) conditionalCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (conditionalSource file) conditionalCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (conditionalSource file) = some (conditionalCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (conditionalSource file) = true ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (conditionalSource file) = false ∧
      Core.HasType inputs.context.values conditionalCore .word) ∧
    (ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (threeSource file) groupedCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (threeSource file) groupedCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (threeSource file) = some (groupedCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (threeSource file) = false ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (threeSource file) = true ∧
      Core.HasType inputs.context.values groupedCore .word) ∧
    (LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (twoSource file) = some (groupedCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (twoSource file) = false ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (twoSource file) = false ∧
      Core.HasType inputs.context.values groupedCore .word) := by
  have c := conditionalWrapper file
  have g := threeWrapper file
  have e := twoWrapper file
  exact ⟨⟨conditionalChild file, c,
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr c,
      rfl, (nonGroupBoundaries file).1, c.core_hasType⟩,
    ⟨threeChild file, g, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr g,
      rfl, (threeChild file).classified, g.core_hasType⟩,
    ⟨twoChild file, e, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e,
      rfl, (nonGroupBoundaries file).2, e.core_hasType⟩⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word
  (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def runtimeCore : Mode → Core.Expr
  | .lambdaOrdinary => conditionalCore
  | .ordinaryLambda => .apply (.var 0) (.ifE (.var 3) (.var 4) lambdaCore)
  | .lambdaLambda => .apply (.var 0) (.ifE (.var 3) lambdaCore lambdaCore)
  | .allOrdinary => .apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4))
  | .grouped => groupedCore
/-! Every selected Core shape has an independent big-step derivation. -/
theorem independently_executed_unified_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (runtimeCore mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, "x"⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, "x"⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start + 17) ∧ ks = range file start (start + 3) ∧
        ps = range file (start + 3) (start + 6) ∧ p = range file (start + 4) (start + 5) ∧
        pn = range file (start + 4) (start + 5) ∧ bs = range file (start + 6) (start + 17) ∧
        ss = range file (start + 7) (start + 16) ∧ rs = range file (start + 14) (start + 15) ∧
        rn = range file (start + 14) (start + 15) then some ⟨by
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl⟩ else none
  | _ => none
private def exactConditional? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = conditionalSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as, [⟨is, .conditional
      ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon ⟨os, .identifier ⟨ons, "ordinary"⟩⟩⟩]⟩⟩ => do
    let yesEq ← exactLambda? file 13 yes
    if h : cs = range file 0 42 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 42 ∧ is = range file 6 41 ∧ fs = range file 6 10 ∧
        fns = range file 6 10 ∧ q = range file 11 12 ∧ colon = range file 31 32 ∧
        os = range file 33 41 ∧ ons = range file 33 41 then some ⟨by
      rw [yesEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩
    else none
  | _ => none
private def exactTwo? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = twoSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨o, .group ⟨i, .group terminal⟩⟩]⟩⟩ => do
    let terminalEq ← exactLambda? file 8 terminal
    if h : cs = range file 0 28 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 28 ∧ o = range file 6 27 ∧ i = range file 7 26 then some ⟨by
      rw [terminalEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactThree? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = threeSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨o, .group ⟨m, .group ⟨i, .group terminal⟩⟩⟩]⟩⟩ => do
    let terminalEq ← exactLambda? file 9 terminal
    if h : cs = range file 0 30 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 30 ∧ o = range file 6 29 ∧ m = range file 7 28 ∧
        i = range file 8 27 then some ⟨by
      rw [terminalEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def accepted (label text : String) (conditional grouped : Bool) (expected : Core.Expr) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == conditional &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped &&
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed == some (expected, .word)) s!"{label}: route or endpoint changed"
private def verifyExactParses : IO Unit := do
  let (cf, cp) ← parseComplete "adr0325-conditional-exact.sol"
    "apply(flag ? lam(x){return x;} : ordinary)"
  let some ce := exactConditional? cf cp | throw (IO.userError "conditional: exact AST/spans differ")
  proof (ce.down ▸ And.intro (parsed_unified_static_contract cf).1 (conditionalWrapper cf).provenance)
  let (gf, gp) ← parseComplete "adr0325-three-exact.sol" "apply((((lam(x){return x;}))))"
  let some ge := exactThree? gf gp | throw (IO.userError "depth3: exact AST/spans differ")
  proof (ge.down ▸ And.intro (parsed_unified_static_contract gf).2.1 (threeWrapper gf).provenance)
  let (ef, ep) ← parseComplete "adr0325-two-exact.sol" "apply(((lam(x){return x;})))"
  let some ee := exactTwo? ef ep | throw (IO.userError "depth2: exact AST/spans differ")
  proof (ee.down ▸ And.intro (parsed_unified_static_contract ef).2.2 (twoWrapper ef).provenance)
private def runExact (label : String) (low high : Nat) (choice : Bool) (mode : Mode)
    (expected : Core.Evaluates (environment choice) store (runtimeCore mode) (.word seven) store) : IO Unit := do
  match Core.runStateful low (Core.State.initial (runtimeCore mode) (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{label}: completed below exact fuel")
  match actualRun : Core.runStateful high (Core.State.initial (runtimeCore mode) (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{label}: result or store changed"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actualRun) expected)
  | .outOfFuel _ => throw (IO.userError s!"{label}: no result at exact fuel")
  | .fault _ _ => throw (IO.userError s!"{label}: Core faulted")
private def verifyRuntime : IO Unit := do
  for (label, text, mode) in [
      ("lambda-ordinary", "apply(flag ? lam(x){return x;} : ordinary)", Mode.lambdaOrdinary),
      ("ordinary-lambda", "apply(flag ? ordinary : lam(x){return x;})", .ordinaryLambda),
      ("lambda-lambda", "apply(flag ? lam(x){return x;} : lam(y){return y;})", .lambdaLambda)] do
    accepted label text true false (runtimeCore mode)
    for choice in [false, true] do
      runExact s!"{label}-{choice}" 13 14 choice mode (by
        simpa [environment] using independently_executed_unified_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
  accepted "all-ordinary" "apply(flag ? ordinary : ordinary)" false false (runtimeCore .allOrdinary)
  for choice in [false, true] do
    runExact s!"all-ordinary-{choice}" 13 14 choice .allOrdinary (by
      simpa [environment] using independently_executed_unified_core .allOrdinary choice
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
  for (label, text, grouped) in [("depth2", "apply(((lam(x){return x;})))", false),
      ("depth3", "apply((((lam(x){return x;}))))", true),
      ("depth4", "apply(((((lam(x){return x;})))))", true),
      ("depth8", "apply(((((((((lam(x){return x;})))))))))", true)] do
    accepted label text false grouped groupedCore
    runExact label 10 11 false .grouped (by
      simpa [environment] using independently_executed_unified_core .grouped false
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
private def rejected (label text : String) (conditional grouped : Bool) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == conditional &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped &&
    (elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed).isNone) s!"{label}: recognized failure changed"
private def verifyBoundaries : IO Unit := do
  for (label, text) in [
      ("condition-type", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("bad-header", "apply(flag ? lam(x,y){return x;} : ordinary)"),
      ("other-type", "apply(flag ? lam(x){return x;} : wrong)"),
      ("callee-missing", "missing(flag ? lam(x){return x;} : ordinary)"),
      ("mixed-grouped", "apply(flag ? lam(x){return x;} : (lam(y){return y;}))")] do
    rejected label text true false
  for (label, text) in [("group-header", "apply((((lam(x,y){return x;}))))"),
      ("group-body", "apply((((lam(x){return flag;}))))"),
      ("group-nonfunction", "flag((((lam(x){return x;}))))"),
      ("group-missing", "missing((((lam(x){return x;}))))")] do
    rejected label text false true
  for (label, text) in [
      ("grouped-conditional", "apply((flag ? lam(x){return x;} : ordinary))"),
      ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("zero", "apply()"),
      ("multi", "apply(lam(x){return x;},ordinary)"),
      ("top", "flag ? lam(x){return x;} : ordinary")] do
    let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs parsed == elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs parsed) s!"{label}: frozen ADR0322 equality changed"
  for (label, text, expected) in [("direct", "apply(lam(x){return x;})", groupedCore),
      ("one-group", "apply((lam(x){return x;}))", groupedCore),
      ("ordinary0", "apply(ordinary)", .apply (.var 0) (.var 4)),
      ("ordinary1", "apply((ordinary))", .apply (.var 0) (.var 4)),
      ("ordinary3", "apply((((ordinary))))", .apply (.var 0) (.var 4))] do
    accepted label text false false expected
private def exercise : IO Unit := do verifyExactParses; verifyRuntime; verifyBoundaries
end Tests.ADR0325ParsedUnifiedConsumerIndependent
/-! Run all parsed ADR-0325 integration checks. -/
def Tests.adr0325ParsedLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaTests : IO Unit := do
  ADR0325ParsedUnifiedConsumerIndependent.exercise
  IO.println "ADR0325 parsed conditional-first finite-group consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithExpectedLambda
/-! Independent parsed consumer for the source-disjoint ADR0318 application entry. -/

set_option autoImplicit false

namespace Tests.ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedCombinedApplication", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 318
private def foreignOwner := declaration 9318
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29

private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell .word⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩
], by decide⟩
private def types : TypeNameTable := []

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaBody (file : Syntax.SourceFile) : Syntax.Block :=
  ⟨range file 12 23,
    [⟨range file 13 22, .returnStmt (some (reference file 20 21 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 23, .lambda (range file 6 9)
    ⟨range file 9 12,
      [⟨range file 10 11, .inferred ⟨range file 10 11, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def directSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [lambdaArgument file]⟩⟩
private def ordinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 15, .call (reference file 0 5 "apply")
    ⟨range file 5 15, [reference file 6 14 "ordinary"]⟩⟩

private def directCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)

private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem lambdaElaboration (file : Syntax.SourceFile) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaArgument file)
        (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, lambdaBody file, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem expectedApplicationElaboration (file : Syntax.SourceFile) :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (directSource file) directCore .word :=
  .application (calleeElaboration file) (lambdaElaboration file)

private theorem expectedCombinedElaboration (file : Syntax.SourceFile) :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (directSource file) directCore .word :=
  .expected rfl (expectedApplicationElaboration file)

private theorem ordinaryArgumentElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 6 14 "ordinary") (.var 4) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
        (.tail (by change "apply" ≠ "ordinary"; decide)
          (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))

private theorem ordinaryRecursiveElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ordinarySource file) ordinaryCore .word :=
  .application (calleeElaboration file) (ordinaryArgumentElaboration file)

private theorem ordinaryCombinedElaboration (file : Syntax.SourceFile) :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (ordinarySource file) ordinaryCore .word :=
  .ordinary rfl (ordinaryRecursiveElaboration file)

/-- Both source-selected children are constructed before executable correspondence is used. -/
theorem parsed_direct_and_ordinary_static_contract
    (directFile ordinaryFile : Syntax.SourceFile) :
    isDirectExpectedLambdaArgumentApplication (directSource directFile) = true ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (directSource directFile) directCore .word ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs (directSource directFile) = some (directCore, .word) ∧
    Core.HasType inputs.context.values directCore .word ∧
    isDirectExpectedLambdaArgumentApplication (ordinarySource ordinaryFile) = false ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (ordinarySource ordinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) = some (ordinaryCore, .word) ∧
    Core.HasType inputs.context.values ordinaryCore .word := by
  have directEvidence := expectedCombinedElaboration directFile
  have ordinaryEvidence := ordinaryCombinedElaboration ordinaryFile
  have directChecked := elaborateLocalApplicationWithExpectedLambda?_iff.mpr directEvidence
  have ordinaryChecked := elaborateLocalApplicationWithExpectedLambda?_iff.mpr ordinaryEvidence
  exact ⟨rfl, directEvidence, directChecked, directEvidence.core_hasType,
    rfl, ordinaryEvidence, ordinaryChecked, ordinaryEvidence.core_hasType⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The direct branch's Core endpoint is independent of unrelated rows and store contents. -/
theorem independently_executed_expected_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      directCore (.word seven) initialStore := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd &&
      parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")

private def rejected (label text : String) (direct : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0318-{label}.sol" text
  check (isDirectExpectedLambdaArgumentApplication parsed == direct)
    s!"{label}: source-shape classifier changed"
  if direct then
    check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed).isNone
      s!"{label}: rejected expected branch unexpectedly accepted"
  check (elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed).isNone
    s!"{label}: combined entry unexpectedly accepted"

private def verifyDirectParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0318-direct.sol"
    "apply(lam(x){return x;})"
  match shape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨lambdaSpan, .lambda keywordSpan
        ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
        ⟨bodySpan, [⟨statementSpan, .returnStmt
          (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 24 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 24 ∧
        lambdaSpan = range file 6 23 ∧ keywordSpan = range file 6 9 ∧
        parametersSpan = range file 9 12 ∧ parameterSpan = range file 10 11 ∧
        parameterNameSpan = range file 10 11 ∧ bodySpan = range file 12 23 ∧
        statementSpan = range file 13 22 ∧ resultSpan = range file 20 21 ∧
        resultNameSpan = range file 20 21 then
      have parsedEq : parsed = directSource file := by
        rcases spans with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed ==
        some (directCore, .word)) "direct: exact checker result changed"
      proof (show elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed =
          some (directCore, .word) from by
        rw [parsedEq]
        exact elaborateLocalApplicationWithExpectedLambda?_iff.mpr
          (expectedCombinedElaboration file))
      pure file
    else throw (IO.userError "direct: exact nested spans differ")
  | _ => throw (IO.userError "direct: exact parsed AST differs")

private def verifyOrdinaryParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0318-ordinary.sol" "apply(ordinary)"
  match shape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan,
        [⟨argumentSpan, .identifier ⟨argumentNameSpan, "ordinary"⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 15 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 15 ∧
        argumentSpan = range file 6 14 ∧ argumentNameSpan = range file 6 14 then
      have parsedEq : parsed = ordinarySource file := by
        rcases spans with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (!isDirectExpectedLambdaArgumentApplication parsed &&
        elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed ==
          some (ordinaryCore, .word)) "ordinary: disjoint legacy result changed"
      proof (show elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed =
          some (ordinaryCore, .word) from by
        rw [parsedEq]
        exact elaborateLocalApplicationWithExpectedLambda?_iff.mpr
          (ordinaryCombinedElaboration file))
      pure file
    else throw (IO.userError "ordinary: exact nested spans differ")
  | _ => throw (IO.userError "ordinary: exact parsed AST differs")

private def exercise : IO Unit := do
  let directFile ← verifyDirectParse
  let ordinaryFile ← verifyOrdinaryParse
  proof (parsed_direct_and_ordinary_static_contract directFile ordinaryFile)

  match Core.runStateful 10 (Core.State.initial directCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial directCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store directCore (.word seven) store := by
      simpa [environment] using independently_executed_expected_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "bad-body" "apply(lam(x){return flag;})" true
  rejected "bad-header" "apply(lam(x,y){return x;})" true
  rejected "grouped-lambda" "apply((lam(x){return x;}))"
  rejected "nested-lambda" "ordinary(apply(lam(x){return x;}))"
  rejected "nonfunction" "flag(lam(x){return x;})" true
  rejected "empty-arity" "apply()"
  rejected "many-arity" "apply(lam(x){return x;},ordinary)"
  rejected "top-level-lambda" "lam(x){return x;}"
  rejected "top-level-identifier" "ordinary"
  rejected "conditional-argument" "apply(flag ? lam(x){return x;} : ordinary)"
  rejected "tuple-argument" "apply((lam(x){return x;},ordinary))"
  rejected "return-boundary" "apply(lam(x){return lam(y){return y;};})" true
  rejected "inferred-let-boundary"
    "apply(lam(x){let y = lam(z){return z;};return x;})" true

end Tests.ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent


def Tests.adr0318LocalApplicationWithExpectedLambdaTests : IO Unit := do
  ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0318 parsed combined application consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda
set_option autoImplicit false
namespace Tests.ADR0335ParsedLocalApplicationWithFiveLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedFiveGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 335
private def foreignOwner := declaration 9335
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 18 "x"
  | .ordinaryLambda => reference file 18 26 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 38 46 "ordinary"
  | .ordinaryLambda => lambdaAt file 29 "x"
  | .lambdaLambda => lambdaAt file 38 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 36 37
  | .ordinaryLambda => range file 27 28
private def conditionalStop : Mode → Nat | .lambdaLambda => 55 | _ => 46
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 6), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 6),
    [⟨range file 6 (stop + 5), .group ⟨range file 7 (stop + 4), .group
      ⟨range file 8 (stop + 3), .group ⟨range file 9 (stop + 2), .group
        ⟨range file 10 (stop + 1), .group ⟨range file 11 stop, .conditional
          (reference file 11 15 "flag") (range file 16 17)
          (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 11 15 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 18 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 18 26)
  | lambdaLambda => exact .expected rfl (lambdaE file 18 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 38 46)
  | ordinaryLambda => exact .expected rfl (lambdaE file 29 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 38 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .fiveLevelGroupedConditional (childE file mode).classified (childE file mode)
theorem parsed_five_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; rcases oldBoundaries file mode with ⟨four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  exact ⟨child, wrapped, child.classified, four, three, two, one, immediate, generic,
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional child.classified, elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, route, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_five_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply((((((flag ? lam(x){return x;} : ordinary))))))" | .ordinaryLambda => "apply((((((flag ? ordinary : lam(x){return x;}))))))" | .lambdaLambda => "apply((((((flag ? lam(x){return x;} : lam(y){return y;}))))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨deepest, .group
        ⟨innermost, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+6) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+6) ∧ outer = range file 6 (conditionalStop mode+5) ∧ middle = range file 7 (conditionalStop mode+4) ∧ inner = range file 8 (conditionalStop mode+3) ∧ deepest = range file 9 (conditionalStop mode+2) ∧ innermost = range file 10 (conditionalStop mode+1) ∧ is = range file 11 (conditionalStop mode) ∧ fs = range file 11 15 ∧ fns = range file 11 15 ∧ q = range file 16 17 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 18 "x" yes; let n ← exactReference? file 38 46 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 18 26 "ordinary" yes; let n ← exactLambda? file 29 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 18 "x" yes; let n ← exactLambda? file 38 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional4 | conditional6 | lambda5
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional4 => callAt file 50 ⟨range file 6 49, .group ⟨range file 7 48, .group ⟨range file 8 47, .group ⟨range file 9 46, .group (conditionalAt file 10)⟩⟩⟩⟩
  | .conditional6 => callAt file 54 ⟨range file 6 53, .group ⟨range file 7 52, .group ⟨range file 8 51, .group ⟨range file 9 50, .group ⟨range file 10 49, .group ⟨range file 11 48, .group (conditionalAt file 12)⟩⟩⟩⟩⟩⟩
  | .lambda5 => callAt file 34 ⟨range file 6 33, .group ⟨range file 7 32, .group ⟨range file 8 31, .group ⟨range file 9 30, .group ⟨range file 10 29, .group (lambdaAt file 11 "x")⟩⟩⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional4, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 10 14 "flag" condition; let y ← exactLambda? file 17 "x" yes; let n ← exactReference? file 37 45 "ordinary" no
    if h : cs=range file 0 50 ∧ as=range file 5 50 ∧ a=range file 6 49 ∧ b=range file 7 48 ∧ c=range file 8 47 ∧ d=range file 9 46 ∧ is=range file 10 45 ∧ q=range file 15 16 ∧ colon=range file 35 36 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional6, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let flag ← exactReference? file 12 16 "flag" condition; let y ← exactLambda? file 19 "x" yes; let n ← exactReference? file 39 47 "ordinary" no
    if h : cs=range file 0 54 ∧ as=range file 5 54 ∧ a=range file 6 53 ∧ b=range file 7 52 ∧ c=range file 8 51 ∧ d=range file 9 50 ∧ e=range file 10 49 ∧ f=range file 11 48 ∧ is=range file 12 47 ∧ q=range file 17 18 ∧ colon=range file 37 38 then some ⟨by rw [ca.down,flag.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda5, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group body⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let bodyEq ← exactLambda? file 11 "x" body
    if h : cs=range file 0 34 ∧ as=range file 5 34 ∧ a=range file 6 33 ∧ b=range file 7 32 ∧ c=range file 8 31 ∧ d=range file 9 30 ∧ e=range file 10 29 then some ⟨by rw [ca.down,bodyEq.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0335-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_five_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0335-{label}.sol" text
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_fiveLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((((((wrong ? lam(x){return x;} : ordinary))))))"),
      ("condition-missing", "apply((((((missing ? lam(x){return x;} : ordinary))))))"),
      ("header", "apply((((((flag ? lam(x,y){return x;} : ordinary))))))"),
      ("body", "apply((((((flag ? lam(x){return flag;} : ordinary))))))"),
      ("other-type", "apply((((((flag ? lam(x){return x;} : wrong))))))"),
      ("other-missing", "apply((((((flag ? lam(x){return x;} : missing))))))"),
      ("nonfunction", "flag((((((flag ? lam(x){return x;} : ordinary))))))"),
      ("callee-missing", "globalApply((((((flag ? lam(x){return x;} : ordinary))))))"),
      ("mixed-grouped", "apply((((((flag ? lam(x){return x;} : (lam(y){return y;})))))))"),
      ("mixed-nested", "apply((((((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0335-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0333 Option changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0333 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) none
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" (some (conditionalCore, .word)) none
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" (some (conditionalCore, .word)) (some .conditional4)
  preserved "six-group-conditional" "apply(((((((flag ? lam(x){return x;} : ordinary)))))))" none (some .conditional6)
  preserved "all-ordinary" "apply((((((flag ? ordinary : ordinary))))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))"),
      (5, "five-lambda-groups", "apply((((((lam(x){return x;}))))))"),
      (6, "six-lambda-groups", "apply(((((((lam(x){return x;})))))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 5 then some .lambda5 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply((((((flag ? (lam(x){return x;}) : ordinary))))))"),
      ("nested-only", "apply((((((flag ? ordinary(lam(x){return x;}) : ordinary))))))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0332-failure", "apply(((((wrong ? lam(x){return x;} : ordinary)))))"), ("adr0330-failure", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode; for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_five_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_five_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0335ParsedLocalApplicationWithFiveLevelGroupedConditionalConsumerIndependent
def Tests.adr0335ParsedLocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0335ParsedLocalApplicationWithFiveLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0335 parsed local five-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithFourLevelGroupedConditionalExpectedLambda
set_option autoImplicit false
namespace Tests.ADR0333ParsedLocalApplicationWithFourLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedFourGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 333
private def foreignOwner := declaration 9333
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 17 "x"
  | .ordinaryLambda => reference file 17 25 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 37 45 "ordinary"
  | .ordinaryLambda => lambdaAt file 28 "x"
  | .lambdaLambda => lambdaAt file 37 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 35 36
  | .ordinaryLambda => range file 26 27
private def conditionalStop : Mode → Nat | .lambdaLambda => 54 | _ => 45
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 5), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 5),
    [⟨range file 6 (stop + 4), .group ⟨range file 7 (stop + 3), .group
      ⟨range file 8 (stop + 2), .group ⟨range file 9 (stop + 1), .group
        ⟨range file 10 stop, .conditional (reference file 10 14 "flag") (range file 15 16)
          (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 10 14 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 17 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 17 25)
  | lambdaLambda => exact .expected rfl (lambdaE file 17 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 37 45)
  | ordinaryLambda => exact .expected rfl (lambdaE file 28 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 37 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .fourLevelGroupedConditional (childE file mode).classified (childE file mode)
theorem parsed_four_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧ Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; have old := oldBoundaries file mode
  exact ⟨child, wrapped, child.classified, old.1, old.2.1, old.2.2.1, old.2.2.2.1, old.2.2.2.2, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional child.classified, elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing old.1, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr} (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_four_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply(((((flag ? lam(x){return x;} : ordinary)))))" | .ordinaryLambda => "apply(((((flag ? ordinary : lam(x){return x;})))))" | .lambdaLambda => "apply(((((flag ? lam(x){return x;} : lam(y){return y;})))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨deepest, .group
        ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+5) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+5) ∧ outer = range file 6 (conditionalStop mode+4) ∧ middle = range file 7 (conditionalStop mode+3) ∧ inner = range file 8 (conditionalStop mode+2) ∧ deepest = range file 9 (conditionalStop mode+1) ∧ is = range file 10 (conditionalStop mode) ∧ fs = range file 10 14 ∧ fns = range file 10 14 ∧ q = range file 15 16 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 17 "x" yes; let n ← exactReference? file 37 45 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 17 25 "ordinary" yes; let n ← exactLambda? file 28 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 17 "x" yes; let n ← exactLambda? file 37 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional3 | conditional5 | lambda4
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional3 => callAt file 48 ⟨range file 6 47, .group ⟨range file 7 46, .group ⟨range file 8 45, .group (conditionalAt file 9)⟩⟩⟩
  | .conditional5 => callAt file 52 ⟨range file 6 51, .group ⟨range file 7 50, .group ⟨range file 8 49, .group ⟨range file 9 48, .group ⟨range file 10 47, .group (conditionalAt file 11)⟩⟩⟩⟩⟩
  | .lambda4 => callAt file 32 ⟨range file 6 31, .group ⟨range file 7 30, .group ⟨range file 8 29, .group ⟨range file 9 28, .group (lambdaAt file 10 "x")⟩⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional3, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 9 13 "flag" condition; let y ← exactLambda? file 16 "x" yes; let n ← exactReference? file 36 44 "ordinary" no
    if h : cs=range file 0 48 ∧ as=range file 5 48 ∧ a=range file 6 47 ∧ b=range file 7 46 ∧ c=range file 8 45 ∧ is=range file 9 44 ∧ q=range file 14 15 ∧ colon=range file 34 35 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional5, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 11 15 "flag" condition; let y ← exactLambda? file 18 "x" yes; let n ← exactReference? file 38 46 "ordinary" no
    if h : cs=range file 0 52 ∧ as=range file 5 52 ∧ a=range file 6 51 ∧ b=range file 7 50 ∧ c=range file 8 49 ∧ d=range file 9 48 ∧ e=range file 10 47 ∧ is=range file 11 46 ∧ q=range file 16 17 ∧ colon=range file 36 37 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda4, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group body⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let bodyEq ← exactLambda? file 10 "x" body
    if h : cs=range file 0 32 ∧ as=range file 5 32 ∧ a=range file 6 31 ∧ b=range file 7 30 ∧ c=range file 8 29 ∧ d=range file 9 28 then some ⟨by rw [ca.down,bodyEq.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0333-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_four_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0333-{label}.sol" text
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_fourLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply(((((wrong ? lam(x){return x;} : ordinary)))))"),
      ("condition-missing", "apply(((((missing ? lam(x){return x;} : ordinary)))))"),
      ("header", "apply(((((flag ? lam(x,y){return x;} : ordinary)))))"),
      ("body", "apply(((((flag ? lam(x){return flag;} : ordinary)))))"),
      ("other-type", "apply(((((flag ? lam(x){return x;} : wrong)))))"),
      ("other-missing", "apply(((((flag ? lam(x){return x;} : missing)))))"),
      ("nonfunction", "flag(((((flag ? lam(x){return x;} : ordinary)))))"),
      ("callee-missing", "globalApply(((((flag ? lam(x){return x;} : ordinary)))))"),
      ("mixed-grouped", "apply(((((flag ? lam(x){return x;} : (lam(y){return y;}))))))"),
      ("mixed-nested", "apply(((((flag ? lam(x){return x;} : ordinary(lam(y){return y;}))))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0333-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0331 Option changed"
  if boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0331 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) none
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" (some (conditionalCore, .word)) (some .conditional3)
  preserved "five-group-conditional" "apply((((((flag ? lam(x){return x;} : ordinary))))))" none (some .conditional5)
  preserved "all-ordinary" "apply(((((flag ? ordinary : ordinary)))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))"),
      (5, "five-lambda-groups", "apply((((((lam(x){return x;}))))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 4 then some .lambda4 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply(((((flag ? (lam(x){return x;}) : ordinary)))))"),
      ("nested-only", "apply(((((flag ? ordinary(lam(x){return x;}) : ordinary)))))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0330-failure", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_four_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_four_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0333ParsedLocalApplicationWithFourLevelGroupedConditionalConsumerIndependent
def Tests.adr0333ParsedLocalApplicationWithFourLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0333ParsedLocalApplicationWithFourLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0333 parsed local four-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithGroupedExpectedLambda
/-! Independent parsed consumer for the group-first ADR-0320 entry. -/

set_option autoImplicit false

namespace Tests.ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGroupFirstApplication", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 320
private def foreignOwner := declaration 9320
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell .word⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩
], by decide⟩
private def types : TypeNameTable := []

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaBody (file : Syntax.SourceFile) (shift : Nat) : Syntax.Block :=
  ⟨range file (12 + shift) (23 + shift),
    [⟨range file (13 + shift) (22 + shift), .returnStmt
      (some (reference file (20 + shift) (21 + shift) "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) (shift : Nat) : Syntax.Expr :=
  ⟨range file (6 + shift) (23 + shift), .lambda (range file (6 + shift) (9 + shift))
    ⟨range file (9 + shift) (12 + shift),
      [⟨range file (10 + shift) (11 + shift), .inferred
        ⟨range file (10 + shift) (11 + shift), "x"⟩⟩]⟩
    none (lambdaBody file shift)⟩
private def directSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [lambdaArgument file 0]⟩⟩
private def groupedSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 26, .call (reference file 0 5 "apply")
    ⟨range file 5 26, [⟨range file 6 25, .group (lambdaArgument file 1)⟩]⟩⟩
private def ordinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 15, .call (reference file 0 5 "apply")
    ⟨range file 5 15, [reference file 6 14 "ordinary"]⟩⟩
private def groupedOrdinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 17, .call (reference file 0 5 "apply")
    ⟨range file 5 17,
      [⟨range file 6 16, .group (reference file 7 15 "ordinary")⟩]⟩⟩

private def expectedCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem lambdaElaboration (file : Syntax.SourceFile) (shift : Nat) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaArgument file shift)
        (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, lambdaBody file shift, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 4) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
        (.tail (by change "apply" ≠ "ordinary"; decide)
          (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))

private theorem groupedEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedSource file) expectedCore .word :=
  .grouped rfl (.application (calleeElaboration file) (lambdaElaboration file 1))
private theorem directEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (directSource file) expectedCore .word :=
  .existing rfl (.expected rfl
    (.application (calleeElaboration file) (lambdaElaboration file 0)))
private theorem ordinaryEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (ordinarySource file) ordinaryCore .word :=
  .existing rfl (.ordinary rfl
    (.application (calleeElaboration file) (ordinaryElaboration file 6 14)))
private theorem groupedOrdinaryEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedOrdinarySource file) ordinaryCore .word :=
  .existing rfl (.ordinary rfl
    (.application (calleeElaboration file) (.group (ordinaryElaboration file 7 15))))

/-- Parsed representatives independently cover all three semantic leaves and grouped ordinary. -/
theorem parsed_three_way_static_contract
    (groupedFile directFile ordinaryFile groupedOrdinaryFile : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedSource groupedFile) expectedCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedSource groupedFile) = some (expectedCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedSource groupedFile) =
        elaborateGroupedExpectedLambdaArgumentApplication?
          types owner inputs (groupedSource groupedFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (directSource directFile) expectedCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (directSource directFile) = some (expectedCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (directSource directFile) =
        elaborateLocalApplicationWithExpectedLambda? types owner inputs (directSource directFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (ordinarySource ordinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) = some (ordinaryCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) =
        elaborateLocalApplicationWithExpectedLambda? types owner inputs (ordinarySource ordinaryFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) = some (ordinaryCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) =
        elaborateLocalApplicationWithExpectedLambda?
          types owner inputs (groupedOrdinarySource groupedOrdinaryFile) := by
  have grouped := groupedEvidence groupedFile
  have direct := directEvidence directFile
  have ordinary := ordinaryEvidence ordinaryFile
  have groupedOrdinary := groupedOrdinaryEvidence groupedOrdinaryFile
  exact ⟨grouped, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr grouped,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl,
    direct, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr direct,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    ordinary, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr ordinary,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    groupedOrdinary, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedOrdinary,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The grouped and direct branches share this independently executed Core endpoint. -/
theorem independently_executed_expected_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      expectedCore (.word seven) initialStore := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd &&
      parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def parseExact (path text : String) (expected : Syntax.SourceFile → Syntax.Expr) :
    IO (Syntax.SourceFile × Syntax.Expr) := do
  let (file, parsed) ← parseComplete path text
  check (parsed == expected file) s!"{path}: exact AST or nested spans differ"
  pure (file, parsed)

private def rejected (label text : String) (grouped : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0320-{label}.sol" text
  check (isOneLevelGroupedExpectedLambdaArgumentApplication parsed == grouped)
    s!"{label}: group classifier changed"
  if grouped then
    check (elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs parsed)
      s!"{label}: grouped branch changed"
    check (elaborateGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone s!"{label}: grouped child unexpectedly accepted"
  else
    check (elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed)
      s!"{label}: existing branch changed"
  check (elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs parsed).isNone s!"{label}: unified entry unexpectedly accepted"

private def acceptedExisting (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0320-{label}.sol" text
  check (!isOneLevelGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      some (ordinaryCore, .word)) s!"{label}: existing acceptance changed"

private def exercise : IO Unit := do
  let (groupedFile, groupedParsed) ← parseExact "adr0320-grouped.sol"
    "apply((lam(x){return x;}))" groupedSource
  let (directFile, directParsed) ← parseExact "adr0320-direct.sol"
    "apply(lam(x){return x;})" directSource
  let (ordinaryFile, ordinaryParsed) ← parseExact "adr0320-ordinary.sol"
    "apply(ordinary)" ordinarySource
  let (groupedOrdinaryFile, groupedOrdinaryParsed) ← parseExact
    "adr0320-grouped-ordinary.sol" "apply((ordinary))" groupedOrdinarySource
  proof (parsed_three_way_static_contract
    groupedFile directFile ordinaryFile groupedOrdinaryFile)
  check (isOneLevelGroupedExpectedLambdaArgumentApplication groupedParsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedParsed ==
      some (expectedCore, .word)) "grouped path changed"
  for parsed in [directParsed, ordinaryParsed, groupedOrdinaryParsed] do
    check (!isOneLevelGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
        elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed)
      "existing parsed path changed"
  check (elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs directParsed == some (expectedCore, .word))
    "direct parsed result changed"
  for parsed in [ordinaryParsed, groupedOrdinaryParsed] do
    check (elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs parsed == some (ordinaryCore, .word))
      "ordinary parsed result changed"

  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_expected_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  acceptedExisting "double-ordinary-group" "apply(((ordinary)))"
  acceptedExisting "triple-ordinary-group" "apply((((ordinary))))"
  rejected "bad-grouped-body" "apply((lam(x){return flag;}))" true
  rejected "bad-grouped-header" "apply((lam(x,y){return x;}))" true
  rejected "grouped-nonfunction" "flag((lam(x){return x;}))" true
  rejected "bad-direct-body" "apply(lam(x){return flag;})"
  rejected "double-lambda-group" "apply(((lam(x){return x;})))"
  rejected "triple-lambda-group" "apply((((lam(x){return x;}))))"
  rejected "global-callee" "globalApply((lam(x){return x;}))" true
  rejected "nested-call" "ordinary(apply((lam(x){return x;})))"
  rejected "call-inside-group" "apply((ordinary(lam(x){return x;})))"
  rejected "tuple" "apply((lam(x){return x;},ordinary))"
  rejected "conditional" "apply((flag ? lam(x){return x;} : ordinary))"
  rejected "empty-arity" "apply()"
  rejected "many-arity" "apply((lam(x){return x;}),ordinary)"
  rejected "top-group" "(lam(x){return x;})"
  rejected "top-lambda" "lam(x){return x;}"
  rejected "top-identifier" "ordinary"
  rejected "return-boundary" "apply((lam(x){return lam(y){return y;};}))" true
  rejected "inferred-let-boundary"
    "apply((lam(x){let y = lam(z){return z;};return x;}))" true

end Tests.ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent

def Tests.adr0320ParsedLocalApplicationWithGroupedExpectedLambdaTests : IO Unit := do
  ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0320 parsed group-first application consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithOneLevelGroupedConditionalExpectedLambda
/-! Parsed consumer for grouped-conditional-first local application dispatch. -/
set_option autoImplicit false
namespace Tests.ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private inductive Existing where | conditional | depthTwo | depthThree
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnifiedGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 327
private def foreignOwner := declaration 9327
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start+17), .lambda (range file start (start+3)) ⟨range file (start+3) (start+6),
    [⟨range file (start+4) (start+5), .inferred ⟨range file (start+4) (start+5), name⟩⟩]⟩ none
    ⟨range file (start+6) (start+17), [⟨range file (start+7) (start+16),
      .returnStmt (some (reference file (start+14) (start+15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 14 "x" | .ordinaryLambda => reference file 14 22 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 34 42 "ordinary" | .ordinaryLambda => lambdaAt file 25 "x" | .lambdaLambda => lambdaAt file 34 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 32 33 | .ordinaryLambda => range file 23 24
private def conditionalStop : Mode → Nat | .lambdaLambda => 51 | _ => 42
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop+2), .call (reference file 0 5 "apply") ⟨range file 5 (stop+2),
    [⟨range file 6 (stop+1), .group ⟨range file 7 stop, .conditional (reference file 7 11 "flag")
      (range file 12 13) (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩]⟩⟩
private def existingSource (file : Syntax.SourceFile) : Existing → Syntax.Expr
  | .conditional => ⟨range file 0 42, .call (reference file 0 5 "apply") ⟨range file 5 42,
      [⟨range file 6 41, .conditional (reference file 6 10 "flag") (range file 11 12)
        (lambdaAt file 13 "x") (range file 31 32) (reference file 33 41 "ordinary")⟩]⟩⟩
  | .depthTwo => ⟨range file 0 28, .call (reference file 0 5 "apply") ⟨range file 5 28,
      [⟨range file 6 27, .group ⟨range file 7 26, .group (lambdaAt file 8 "x")⟩⟩]⟩⟩
  | .depthThree => ⟨range file 0 30, .call (reference file 0 5 "apply") ⟨range file 5 30,
      [⟨range file 6 29, .group ⟨range file 7 28, .group ⟨range file 8 27,
        .group (lambdaAt file 9 "x")⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def conditionalCore (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private def groupedCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 7 11 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start+6) (start+17), [⟨range file (start+7) (start+16), .returnStmt (some (reference file (start+14) (start+15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with | lambdaOrdinary => exact .expected rfl (lambdaE file 14 "x") | ordinaryLambda => exact .ordinary rfl (ordinaryE file 14 22) | lambdaLambda => exact .expected rfl (lambdaE file 14 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 34 42) | ordinaryLambda => exact .expected rfl (lambdaE file 25 "x") | lambdaLambda => exact .expected rfl (lambdaE file 34 "y")
private theorem sourceE (file : Syntax.SourceFile) (mode : Mode) : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (conditionalCore mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) : isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  constructor
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro selected
    obtain ⟨_,_,_,_,_,spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
    cases spine with | group child => cases child
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (conditionalCore mode) .word := .oneLevelGroupedConditional (sourceE file mode).classified (sourceE file mode)
/-- Parsed new sources and every old source retain the complete selected child Option. -/
theorem parsed_unified_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (conditionalCore mode) .word ∧
    LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (conditionalCore mode) .word ∧
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (conditionalCore mode, .word) ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (conditionalCore mode, .word) ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    Core.HasType inputs.context.values (conditionalCore mode) .word ∧
    ∀ old, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication old = false →
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs old = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs old := by
  have child := sourceE file mode; have wrapped := wrapperE file mode; have old := oldBoundaries file mode
  exact ⟨child, wrapped, child.classified, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, old.1, old.2,
    wrapped.core_hasType, fun _ boundary => elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing boundary⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Conditional and grouped-lambda child Cores execute independently with exact store preservation. -/
theorem independently_executed_wrapper_cores (mode : Mode) (choice : Bool) (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow] initialStore (conditionalCore mode) (.word seven) initialStore ∧
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow] initialStore groupedCore (.word seven) initialStore := by
  constructor
  · cases mode <;> cases choice
    · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply((flag ? lam(x){return x;} : ordinary))" | .ordinaryLambda => "apply((flag ? ordinary : lam(x){return x;}))" | .lambdaLambda => "apply((flag ? lam(x){return x;} : lam(y){return y;}))"
private def existingText : Existing → String | .conditional => "apply(flag ? lam(x){return x;} : ordinary)" | .depthTwo => "apply(((lam(x){return x;})))" | .depthThree => "apply((((lam(x){return x;}))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next => check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file) s!"{path}: parser/EOF/span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String) (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ => if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name then some ⟨by rcases h with ⟨rfl,rfl,rfl⟩; rfl⟩ else none | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String) (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls=range file start (start+17) ∧ ks=range file start (start+3) ∧ ps=range file (start+3) (start+6) ∧ p=range file (start+4) (start+5) ∧ pn=range file (start+4) (start+5) ∧ observed=name ∧ bs=range file (start+6) (start+17) ∧ ss=range file (start+7) (start+16) ∧ rs=range file (start+14) (start+15) ∧ rn=range file (start+14) (start+15) ∧ result=name then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as, [⟨gs, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩]⟩⟩ =>
    if h : cs=range file 0 (conditionalStop mode+2) ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 (conditionalStop mode+2) ∧ gs=range file 6 (conditionalStop mode+1) ∧ is=range file 7 (conditionalStop mode) ∧ fs=range file 7 11 ∧ fns=range file 7 11 ∧ q=range file 12 13 ∧ colon=colonRange file mode then
      match mode with
      | .lambdaOrdinary => do let y ← exactLambda? file 14 "x" yes; let n ← exactReference? file 34 42 "ordinary" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
      | .ordinaryLambda => do let y ← exactReference? file 14 22 "ordinary" yes; let n ← exactLambda? file 25 "x" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
      | .lambdaLambda => do let y ← exactLambda? file 14 "x" yes; let n ← exactLambda? file 34 "y" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
    else none
  | _ => none
private def exactExisting? (file : Syntax.SourceFile) (route : Existing) (candidate : Syntax.Expr) : Option (PLift (candidate = existingSource file route)) :=
  match route, candidate with
  | .conditional, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩]⟩⟩ =>
    if h : cs=range file 0 42 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 42 ∧ is=range file 6 41 ∧ fs=range file 6 10 ∧ fns=range file 6 10 ∧ q=range file 11 12 ∧ colon=range file 31 32 then do
      let y ← exactLambda? file 13 "x" yes; let n ← exactReference? file 33 41 "ordinary" no
      some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | .depthTwo, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨inner, .group term⟩⟩]⟩⟩ =>
    if h : cs=range file 0 28 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 28 ∧ outer=range file 6 27 ∧ inner=range file 7 26 then do
      let child ← exactLambda? file 8 "x" term
      some ⟨by rw [child.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | .depthThree, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨first, .group ⟨second, .group ⟨third, .group term⟩⟩⟩]⟩⟩ =>
    if h : cs=range file 0 30 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 30 ∧ first=range file 6 29 ∧ second=range file 7 28 ∧ third=range file 8 27 then do
      let child ← exactLambda? file 9 "x" term
      some ⟨by rw [child.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file,parsed) ← parseComplete s!"adr0327-{label mode}.sol" (modeText mode)
  let some eq := exactSource? file mode parsed | throw (IO.userError "new exact AST/spans")
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed == some (conditionalCore mode,.word) && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == some (conditionalCore mode,.word)) s!"{label mode}: new route"
  proof (eq.down ▸ parsed_unified_static_contract file mode); proof (sourceE file mode).provenance; proof (wrapperE file mode).provenance
private def verifyExisting (route : Existing) : IO Unit := do
  let (file,parsed) ← parseComplete "adr0327-existing.sol" (existingText route)
  let some eq := exactExisting? file route parsed | throw (IO.userError "existing exact AST/spans")
  let expected := match route with | .conditional => some (conditionalCore .lambdaOrdinary,.word) | .depthTwo | .depthThree => some (groupedCore,.word)
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == expected && elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed == expected) "existing exact Option"
  proof eq.down
  proof (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing
    (types := types) (owner := owner) (inputs := inputs) (source := existingSource file route)
    (by cases route <;> rfl))
private def rejected (label text : String) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text
  let child := elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed; let wrapped := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone && wrapped.isNone && wrapped == child) s!"{label}: selected failure"
private def inheritedFailure (label text : String) (conditional grouped : Bool) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text; let wrapped := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed; let old := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && isConditionalExpectedLambdaArgumentApplication parsed == conditional && isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped && wrapped.isNone && wrapped == old) s!"{label}: inherited failure"
private def verifyFailures : IO Unit := do
  for (label,text) in [("condition-type","apply((wrong ? lam(x){return x;} : ordinary))"),("condition-missing","apply((missing ? lam(x){return x;} : ordinary))"),("header","apply((flag ? lam(x,y){return x;} : ordinary))"),("body","apply((flag ? lam(x){return flag;} : ordinary))"),("other-type","apply((flag ? lam(x){return x;} : wrong))"),("other-missing","apply((flag ? lam(x){return x;} : missing))"),("nonfunction","flag((flag ? lam(x){return x;} : ordinary))"),("mixed-grouped","apply((flag ? lam(x){return x;} : (lam(y){return y;})))"),("mixed-nested","apply((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))"),("callee-missing","globalApply((flag ? lam(x){return x;} : ordinary))")] do rejected label text
  inheritedFailure "old-conditional" "apply(flag ? lam(x,y){return x;} : ordinary)" true false
  inheritedFailure "old-grouped" "apply((((lam(x,y){return x;}))))" false true
private def preserved (label text : String) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed) s!"{label}: predecessor Option"
private def verifyPreservation : IO Unit := do
  for route in [Existing.conditional,.depthTwo,.depthThree] do verifyExisting route
  for (label,text) in [("direct","apply(lam(x){return x;})"),("one-group","apply((lam(x){return x;}))"),("ordinary","apply(ordinary)"),("all-ordinary","apply((flag ? ordinary : ordinary))"),("branch-grouped","apply(flag ? (lam(x){return x;}) : ordinary)"),("two-outer","apply(((flag ? lam(x){return x;} : ordinary)))"),("zero","apply()"),("multi","apply(lam(x){return x;},ordinary)"),("top","(flag ? lam(x){return x;} : ordinary)"),("tuple","apply((lam(x){return x;},ordinary))"),("nested","apply(ordinary(lam(x){return x;}))")] do preserved label text
private def runExact (below complete : Nat) (core : Core.Expr) (choice : Bool) (expected : Core.Evaluates (environment choice) store core (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial core (environment choice) store) with | .outOfFuel _ => pure () | _ => throw (IO.userError "completed early")
  match actual : Core.runStateful complete (Core.State.initial core (environment choice) store) with
  | .done value finalStore => check (value == .word seven && finalStore == store) "result/store"; proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError "out at boundary") | .fault _ _ => throw (IO.userError "fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary,.ordinaryLambda,.lambdaLambda] do
    verifySuccess mode
    for choice in [false,true] do
      let evidence := independently_executed_wrapper_cores mode choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
      runExact 13 14 (conditionalCore mode) choice (by simpa [environment] using evidence.1)
  for choice in [false,true] do let evidence := independently_executed_wrapper_cores .lambdaOrdinary choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store; runExact 10 11 groupedCore choice (by simpa [environment] using evidence.2)
  verifyFailures; verifyPreservation
end Tests.ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent
/-- Run all parsed ADR-0327 grouped-conditional-first checks. -/
def Tests.adr0327ParsedLocalApplicationWithOneLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent.exercise
  IO.println "ADR0327 parsed grouped-conditional-first consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda
set_option autoImplicit false
namespace Tests.ADR0339ParsedLocalApplicationWithSevenLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedSevenGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 339
private def foreignOwner := declaration 9339
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr | .lambdaOrdinary | .lambdaLambda => lambdaAt file 20 "x" | .ordinaryLambda => reference file 20 28 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 40 48 "ordinary"
  | .ordinaryLambda => lambdaAt file 31 "x"
  | .lambdaLambda => lambdaAt file 40 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 38 39
  | .ordinaryLambda => range file 29 30
private def conditionalStop : Mode → Nat | .lambdaLambda => 57 | _ => 48
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 8), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 8),
    [⟨range file 6 (stop + 7), .group ⟨range file 7 (stop + 6), .group
      ⟨range file 8 (stop + 5), .group ⟨range file 9 (stop + 4), .group
        ⟨range file 10 (stop + 3), .group ⟨range file 11 (stop + 2), .group
          ⟨range file 12 (stop + 1), .group ⟨range file 13 stop, .conditional (reference file 13 17 "flag") (range file 18 19)
            (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 13 17 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 20 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 20 28)
  | lambdaLambda => exact .expected rfl (lambdaE file 20 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 40 48)
  | ordinaryLambda => exact .expected rfl (lambdaE file 31 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 40 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .sevenLevelGroupedConditional (childE file mode).classified (childE file mode)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_seven_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧ isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧ elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; rcases oldBoundaries file mode with ⟨six, five, four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) six
  exact ⟨child, wrapped, child.classified, six, five, four, three, two, one, immediate, generic,
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional child.classified, elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, route, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_seven_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply((((((((flag ? lam(x){return x;} : ordinary))))))))" | .ordinaryLambda => "apply((((((((flag ? ordinary : lam(x){return x;}))))))))" | .lambdaLambda => "apply((((((((flag ? lam(x){return x;} : lam(y){return y;}))))))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨deepest, .group
        ⟨innermost, .group ⟨terminal, .group ⟨seventh, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+8) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+8) ∧ outer = range file 6 (conditionalStop mode+7) ∧ middle = range file 7 (conditionalStop mode+6) ∧ inner = range file 8 (conditionalStop mode+5) ∧ deepest = range file 9 (conditionalStop mode+4) ∧ innermost = range file 10 (conditionalStop mode+3) ∧ terminal = range file 11 (conditionalStop mode+2) ∧ seventh = range file 12 (conditionalStop mode+1) ∧ is = range file 13 (conditionalStop mode) ∧ fs = range file 13 17 ∧ fns = range file 13 17 ∧ q = range file 18 19 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 20 "x" yes; let n ← exactReference? file 40 48 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 20 28 "ordinary" yes; let n ← exactLambda? file 31 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 20 "x" yes; let n ← exactLambda? file 40 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional6 | conditional8 | lambda7
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional6 => callAt file 54 ⟨range file 6 53, .group ⟨range file 7 52, .group ⟨range file 8 51, .group ⟨range file 9 50, .group ⟨range file 10 49, .group ⟨range file 11 48, .group (conditionalAt file 12)⟩⟩⟩⟩⟩⟩
  | .conditional8 => callAt file 58 ⟨range file 6 57, .group ⟨range file 7 56, .group ⟨range file 8 55, .group ⟨range file 9 54, .group ⟨range file 10 53, .group ⟨range file 11 52, .group ⟨range file 12 51, .group ⟨range file 13 50, .group (conditionalAt file 14)⟩⟩⟩⟩⟩⟩⟩⟩
  | .lambda7 => callAt file 38 ⟨range file 6 37, .group ⟨range file 7 36, .group ⟨range file 8 35, .group ⟨range file 9 34, .group ⟨range file 10 33, .group ⟨range file 11 32, .group ⟨range file 12 31, .group (lambdaAt file 13 "x")⟩⟩⟩⟩⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional6, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let flag ← exactReference? file 12 16 "flag" condition; let y ← exactLambda? file 19 "x" yes; let n ← exactReference? file 39 47 "ordinary" no
    if h : cs=range file 0 54 ∧ as=range file 5 54 ∧ a=range file 6 53 ∧ b=range file 7 52 ∧ c=range file 8 51 ∧ d=range file 9 50 ∧ e=range file 10 49 ∧ f=range file 11 48 ∧ is=range file 12 47 ∧ q=range file 17 18 ∧ colon=range file 37 38 then some ⟨by rw [ca.down,flag.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional8, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨g, .group ⟨h, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let flag ← exactReference? file 14 18 "flag" condition; let y ← exactLambda? file 21 "x" yes; let n ← exactReference? file 41 49 "ordinary" no
    if exact : cs=range file 0 58 ∧ as=range file 5 58 ∧ a=range file 6 57 ∧ b=range file 7 56 ∧ c=range file 8 55 ∧ d=range file 9 54 ∧ e=range file 10 53 ∧ f=range file 11 52 ∧ g=range file 12 51 ∧ h=range file 13 50 ∧ is=range file 14 49 ∧ q=range file 19 20 ∧ colon=range file 39 40 then some ⟨by rw [ca.down,flag.down,y.down,n.down]; rcases exact with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda7, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨g, .group body⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let bodyEq ← exactLambda? file 13 "x" body
    if exact : cs=range file 0 38 ∧ as=range file 5 38 ∧ a=range file 6 37 ∧ b=range file 7 36 ∧ c=range file 8 35 ∧ d=range file 9 34 ∧ e=range file 10 33 ∧ f=range file 11 32 ∧ g=range file 12 31 then some ⟨by rw [ca.down,bodyEq.down]; rcases exact with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0339-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_seven_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0339-{label}.sol" text
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_of_sevenLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((((((((wrong ? lam(x){return x;} : ordinary))))))))"),
      ("condition-missing", "apply((((((((missing ? lam(x){return x;} : ordinary))))))))"),
      ("header", "apply((((((((flag ? lam(x,y){return x;} : ordinary))))))))"),
      ("body", "apply((((((((flag ? lam(x){return flag;} : ordinary))))))))"),
      ("other-type", "apply((((((((flag ? lam(x){return x;} : wrong))))))))"),
      ("other-missing", "apply((((((((flag ? lam(x){return x;} : missing))))))))"),
      ("nonfunction", "flag((((((((flag ? lam(x){return x;} : ordinary))))))))"),
      ("callee-missing", "globalApply((((((((flag ? lam(x){return x;} : ordinary))))))))"),
      ("mixed-grouped", "apply((((((((flag ? lam(x){return x;} : (lam(y){return y;})))))))))"),
      ("mixed-nested", "apply((((((((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))))))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0339-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0337 Option changed"
  if boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0337 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) none
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" (some (conditionalCore, .word)) none
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" (some (conditionalCore, .word)) none
  preserved "five-group-conditional" "apply((((((flag ? lam(x){return x;} : ordinary))))))" (some (conditionalCore, .word)) none; preserved "six-group-conditional" "apply(((((((flag ? lam(x){return x;} : ordinary)))))))" (some (conditionalCore, .word)) (some .conditional6)
  preserved "eight-group-conditional" "apply(((((((((flag ? lam(x){return x;} : ordinary)))))))))" none (some .conditional8)
  preserved "all-ordinary" "apply((((((((flag ? ordinary : ordinary))))))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))"),
      (5, "five-lambda-groups", "apply((((((lam(x){return x;}))))))"),
      (6, "six-lambda-groups", "apply(((((((lam(x){return x;})))))))"),
      (7, "seven-lambda-groups", "apply((((((((lam(x){return x;}))))))))"), (8, "eight-lambda-groups", "apply(((((((((lam(x){return x;})))))))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 7 then some .lambda7 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply((((((((flag ? (lam(x){return x;}) : ordinary))))))))"),
      ("nested-only", "apply((((((((flag ? ordinary(lam(x){return x;}) : ordinary))))))))"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0336-failure", "apply(((((((wrong ? lam(x){return x;} : ordinary)))))))"), ("adr0334-failure", "apply((((((wrong ? lam(x){return x;} : ordinary))))))"), ("adr0332-failure", "apply(((((wrong ? lam(x){return x;} : ordinary)))))"), ("adr0330-failure", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode; for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_seven_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_seven_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional", "five-group-conditional", "six-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups", "seven-lambda-groups", "eight-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0339ParsedLocalApplicationWithSevenLevelGroupedConditionalConsumerIndependent
def Tests.adr0339ParsedLocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0339ParsedLocalApplicationWithSevenLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0339 parsed local seven-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithSixLevelGroupedConditionalExpectedLambda
set_option autoImplicit false
namespace Tests.ADR0337ParsedLocalApplicationWithSixLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedSixGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 337
private def foreignOwner := declaration 9337
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr | .lambdaOrdinary | .lambdaLambda => lambdaAt file 19 "x" | .ordinaryLambda => reference file 19 27 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 39 47 "ordinary"
  | .ordinaryLambda => lambdaAt file 30 "x"
  | .lambdaLambda => lambdaAt file 39 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 37 38
  | .ordinaryLambda => range file 28 29
private def conditionalStop : Mode → Nat | .lambdaLambda => 56 | _ => 47
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 7), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 7),
    [⟨range file 6 (stop + 6), .group ⟨range file 7 (stop + 5), .group
      ⟨range file 8 (stop + 4), .group ⟨range file 9 (stop + 3), .group
        ⟨range file 10 (stop + 2), .group ⟨range file 11 (stop + 1), .group
          ⟨range file 12 stop, .conditional (reference file 12 16 "flag") (range file 17 18)
            (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 12 16 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 19 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 19 27)
  | lambdaLambda => exact .expected rfl (lambdaE file 19 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 39 47)
  | ordinaryLambda => exact .expected rfl (lambdaE file 30 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 39 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .sixLevelGroupedConditional (childE file mode).classified (childE file mode)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_six_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧ isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; rcases oldBoundaries file mode with ⟨five, four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) five
  exact ⟨child, wrapped, child.classified, five, four, three, two, one, immediate, generic,
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional child.classified, elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, route, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_six_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply(((((((flag ? lam(x){return x;} : ordinary)))))))" | .ordinaryLambda => "apply(((((((flag ? ordinary : lam(x){return x;})))))))" | .lambdaLambda => "apply(((((((flag ? lam(x){return x;} : lam(y){return y;})))))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨deepest, .group
        ⟨innermost, .group ⟨terminal, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+7) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+7) ∧ outer = range file 6 (conditionalStop mode+6) ∧ middle = range file 7 (conditionalStop mode+5) ∧ inner = range file 8 (conditionalStop mode+4) ∧ deepest = range file 9 (conditionalStop mode+3) ∧ innermost = range file 10 (conditionalStop mode+2) ∧ terminal = range file 11 (conditionalStop mode+1) ∧ is = range file 12 (conditionalStop mode) ∧ fs = range file 12 16 ∧ fns = range file 12 16 ∧ q = range file 17 18 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 19 "x" yes; let n ← exactReference? file 39 47 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 19 27 "ordinary" yes; let n ← exactLambda? file 30 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 19 "x" yes; let n ← exactLambda? file 39 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional5 | conditional7 | lambda6
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional5 => callAt file 52 ⟨range file 6 51, .group ⟨range file 7 50, .group ⟨range file 8 49, .group ⟨range file 9 48, .group ⟨range file 10 47, .group (conditionalAt file 11)⟩⟩⟩⟩⟩
  | .conditional7 => callAt file 56 ⟨range file 6 55, .group ⟨range file 7 54, .group ⟨range file 8 53, .group ⟨range file 9 52, .group ⟨range file 10 51, .group ⟨range file 11 50, .group ⟨range file 12 49, .group (conditionalAt file 13)⟩⟩⟩⟩⟩⟩⟩
  | .lambda6 => callAt file 36 ⟨range file 6 35, .group ⟨range file 7 34, .group ⟨range file 8 33, .group ⟨range file 9 32, .group ⟨range file 10 31, .group ⟨range file 11 30, .group (lambdaAt file 12 "x")⟩⟩⟩⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional5, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 11 15 "flag" condition; let y ← exactLambda? file 18 "x" yes; let n ← exactReference? file 38 46 "ordinary" no
    if h : cs=range file 0 52 ∧ as=range file 5 52 ∧ a=range file 6 51 ∧ b=range file 7 50 ∧ c=range file 8 49 ∧ d=range file 9 48 ∧ e=range file 10 47 ∧ is=range file 11 46 ∧ q=range file 16 17 ∧ colon=range file 36 37 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional7, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨g, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let flag ← exactReference? file 13 17 "flag" condition; let y ← exactLambda? file 20 "x" yes; let n ← exactReference? file 40 48 "ordinary" no
    if h : cs=range file 0 56 ∧ as=range file 5 56 ∧ a=range file 6 55 ∧ b=range file 7 54 ∧ c=range file 8 53 ∧ d=range file 9 52 ∧ e=range file 10 51 ∧ f=range file 11 50 ∧ g=range file 12 49 ∧ is=range file 13 48 ∧ q=range file 18 19 ∧ colon=range file 38 39 then some ⟨by rw [ca.down,flag.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda6, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group body⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let bodyEq ← exactLambda? file 12 "x" body
    if h : cs=range file 0 36 ∧ as=range file 5 36 ∧ a=range file 6 35 ∧ b=range file 7 34 ∧ c=range file 8 33 ∧ d=range file 9 32 ∧ e=range file 10 31 ∧ f=range file 11 30 then some ⟨by rw [ca.down,bodyEq.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0337-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_six_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0337-{label}.sol" text
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_sixLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply(((((((wrong ? lam(x){return x;} : ordinary)))))))"),
      ("condition-missing", "apply(((((((missing ? lam(x){return x;} : ordinary)))))))"),
      ("header", "apply(((((((flag ? lam(x,y){return x;} : ordinary)))))))"),
      ("body", "apply(((((((flag ? lam(x){return flag;} : ordinary)))))))"),
      ("other-type", "apply(((((((flag ? lam(x){return x;} : wrong)))))))"),
      ("other-missing", "apply(((((((flag ? lam(x){return x;} : missing)))))))"),
      ("nonfunction", "flag(((((((flag ? lam(x){return x;} : ordinary)))))))"),
      ("callee-missing", "globalApply(((((((flag ? lam(x){return x;} : ordinary)))))))"),
      ("mixed-grouped", "apply(((((((flag ? lam(x){return x;} : (lam(y){return y;}))))))))"),
      ("mixed-nested", "apply(((((((flag ? lam(x){return x;} : ordinary(lam(y){return y;}))))))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0337-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0335 Option changed"
  if boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0335 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) none
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" (some (conditionalCore, .word)) none
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" (some (conditionalCore, .word)) none
  preserved "five-group-conditional" "apply((((((flag ? lam(x){return x;} : ordinary))))))" (some (conditionalCore, .word)) (some .conditional5)
  preserved "seven-group-conditional" "apply((((((((flag ? lam(x){return x;} : ordinary))))))))" none (some .conditional7)
  preserved "all-ordinary" "apply(((((((flag ? ordinary : ordinary)))))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))"),
      (5, "five-lambda-groups", "apply((((((lam(x){return x;}))))))"),
      (6, "six-lambda-groups", "apply(((((((lam(x){return x;})))))))"),
      (7, "seven-lambda-groups", "apply((((((((lam(x){return x;}))))))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 6 then some .lambda6 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply(((((((flag ? (lam(x){return x;}) : ordinary)))))))"),
      ("nested-only", "apply(((((((flag ? ordinary(lam(x){return x;}) : ordinary)))))))"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0334-failure", "apply((((((wrong ? lam(x){return x;} : ordinary))))))"), ("adr0332-failure", "apply(((((wrong ? lam(x){return x;} : ordinary)))))"), ("adr0330-failure", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode; for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_six_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_six_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional", "five-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups", "seven-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0337ParsedLocalApplicationWithSixLevelGroupedConditionalConsumerIndependent
def Tests.adr0337ParsedLocalApplicationWithSixLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0337ParsedLocalApplicationWithSixLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0337 parsed local six-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda
set_option autoImplicit false
namespace Tests.ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedThreeGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 331
private def foreignOwner := declaration 9331
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 16 "x"
  | .ordinaryLambda => reference file 16 24 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 36 44 "ordinary"
  | .ordinaryLambda => lambdaAt file 27 "x"
  | .lambdaLambda => lambdaAt file 36 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 34 35
  | .ordinaryLambda => range file 25 26
private def conditionalStop : Mode → Nat | .lambdaLambda => 53 | _ => 44
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 4), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 4),
    [⟨range file 6 (stop + 3), .group ⟨range file 7 (stop + 2), .group
      ⟨range file 8 (stop + 1), .group ⟨range file 9 stop, .conditional
        (reference file 9 13 "flag") (range file 14 15) (thenSource file mode)
        (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 9 13 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 16 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 16 24)
  | lambdaLambda => exact .expected rfl (lambdaE file 16 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 36 44)
  | ordinaryLambda => exact .expected rfl (lambdaE file 27 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 36 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .threeLevelGroupedConditional (childE file mode).classified (childE file mode)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_three_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧
    isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧ Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; have old := oldBoundaries file mode
  exact ⟨child, wrapped, child.classified, old.1, old.2.1, old.2.2.1, old.2.2.2,
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional child.classified,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing old.1, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_three_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String
  | .lambdaOrdinary => "apply((((flag ? lam(x){return x;} : ordinary))))"
  | .ordinaryLambda => "apply((((flag ? ordinary : lam(x){return x;}))))"
  | .lambdaLambda => "apply((((flag ? lam(x){return x;} : lam(y){return y;}))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨is, .conditional
        ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+4) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+4) ∧ outer = range file 6 (conditionalStop mode+3) ∧ middle = range file 7 (conditionalStop mode+2) ∧ inner = range file 8 (conditionalStop mode+1) ∧ is = range file 9 (conditionalStop mode) ∧ fs = range file 9 13 ∧ fns = range file 9 13 ∧ q = range file 14 15 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 16 "x" yes; let n ← exactReference? file 36 44 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 16 24 "ordinary" yes; let n ← exactLambda? file 27 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 16 "x" yes; let n ← exactLambda? file 36 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional2 | conditional4 | lambda3
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional2 => callAt file 46 ⟨range file 6 45, .group ⟨range file 7 44, .group (conditionalAt file 8)⟩⟩
  | .conditional4 => callAt file 50 ⟨range file 6 49, .group ⟨range file 7 48, .group ⟨range file 8 47, .group ⟨range file 9 46, .group (conditionalAt file 10)⟩⟩⟩⟩
  | .lambda3 => callAt file 30 ⟨range file 6 29, .group ⟨range file 7 28, .group ⟨range file 8 27, .group (lambdaAt file 9 "x")⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional2, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 8 12 "flag" condition; let y ← exactLambda? file 15 "x" yes; let n ← exactReference? file 35 43 "ordinary" no
    if h : cs=range file 0 46 ∧ as=range file 5 46 ∧ o=range file 6 45 ∧ i=range file 7 44 ∧ is=range file 8 43 ∧ q=range file 13 14 ∧ colon=range file 33 34 then some ⟨by rw [c.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional4, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 10 14 "flag" condition; let y ← exactLambda? file 17 "x" yes; let n ← exactReference? file 37 45 "ordinary" no
    if h : cs=range file 0 50 ∧ as=range file 5 50 ∧ a=range file 6 49 ∧ b=range file 7 48 ∧ c=range file 8 47 ∧ d=range file 9 46 ∧ is=range file 10 45 ∧ q=range file 15 16 ∧ colon=range file 35 36 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda3, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group ⟨j, .group body⟩⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let b ← exactLambda? file 9 "x" body
    if h : cs=range file 0 30 ∧ as=range file 5 30 ∧ o=range file 6 29 ∧ i=range file 7 28 ∧ j=range file 8 27 then some ⟨by rw [c.down,b.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0331-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_three_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0331-{label}.sol" text
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("condition-missing", "apply((((missing ? lam(x){return x;} : ordinary))))"),
      ("header", "apply((((flag ? lam(x,y){return x;} : ordinary))))"),
      ("body", "apply((((flag ? lam(x){return flag;} : ordinary))))"),
      ("other-type", "apply((((flag ? lam(x){return x;} : wrong))))"),
      ("other-missing", "apply((((flag ? lam(x){return x;} : missing))))"),
      ("nonfunction", "flag((((flag ? lam(x){return x;} : ordinary))))"),
      ("callee-missing", "globalApply((((flag ? lam(x){return x;} : ordinary))))"),
      ("mixed-grouped", "apply((((flag ? lam(x){return x;} : (lam(y){return y;})))))"),
      ("mixed-nested", "apply((((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0331-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0329 Option changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0329 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) (some .conditional2)
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" none (some .conditional4)
  preserved "all-ordinary" "apply((((flag ? ordinary : ordinary))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 3 then some .lambda3 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply((((flag ? (lam(x){return x;}) : ordinary))))"),
      ("nested-only", "apply((((flag ? ordinary(lam(x){return x;}) : ordinary))))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_three_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_three_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    runExact "immediate-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "one-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "two-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "direct-lambda-control" 10 11 directCore choice (directE choice)
    runExact "finite-group-lambda-control" 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent
def Tests.adr0331ParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0331 parsed local three-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda
/-! Parsed consumer for ADR-0329's two-level-grouped-conditional-first wrapper. -/
set_option autoImplicit false
namespace Tests.ADR0329ParsedLocalApplicationWithTwoLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedTwoGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 329
private def foreignOwner := declaration 9329
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 15 "x"
  | .ordinaryLambda => reference file 15 23 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 35 43 "ordinary"
  | .ordinaryLambda => lambdaAt file 26 "x"
  | .lambdaLambda => lambdaAt file 35 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 33 34
  | .ordinaryLambda => range file 24 25
private def conditionalStop : Mode → Nat | .lambdaLambda => 52 | _ => 43
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 3), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 3),
    [⟨range file 6 (stop + 2), .group ⟨range file 7 (stop + 1), .group
      ⟨range file 8 stop, .conditional (reference file 8 12 "flag") (range file 13 14)
        (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 8 12 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 15 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 15 23)
  | lambdaLambda => exact .expected rfl (lambdaE file 15 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 35 43)
  | ordinaryLambda => exact .expected rfl (lambdaE file 26 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 35 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word :=
  .twoLevelGroupedConditional (childE file mode).classified (childE file mode)
/-! Every parsed success retains the exact child, wrapper route, Core and type. -/
theorem parsed_two_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) =
      elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode
  exact ⟨child, wrapped,
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional child.classified,
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped,
    wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s =
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-! The wrapper's three new Cores evaluate for both choices without changing the store. -/
theorem independently_executed_two_group_wrapper_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String
  | .lambdaOrdinary => "apply(((flag ? lam(x){return x;} : ordinary)))"
  | .ordinaryLambda => "apply(((flag ? ordinary : lam(x){return x;})))"
  | .lambdaLambda => "apply(((flag ? lam(x){return x;} : lam(y){return y;})))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨inner, .group ⟨is, .conditional
        ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+3) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+3) ∧ outer = range file 6 (conditionalStop mode+2) ∧ inner = range file 7 (conditionalStop mode+1) ∧ is = range file 8 (conditionalStop mode) ∧ fs = range file 8 12 ∧ fns = range file 8 12 ∧ q = range file 13 14 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 15 "x" yes; let n ← exactReference? file 35 43 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 15 23 "ordinary" yes; let n ← exactLambda? file 26 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 15 "x" yes; let n ← exactLambda? file 35 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private def oneGroupConditionalSource (file : Syntax.SourceFile) : Syntax.Expr :=
  callAt file 44 ⟨range file 6 43, .group (conditionalAt file 7)⟩
private def immediateConditionalSource (file : Syntax.SourceFile) : Syntax.Expr := callAt file 42 (conditionalAt file 6)
private inductive ExactControl where | immediate | oneGroup | lambda2 | lambda3
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .immediate => immediateConditionalSource file | .oneGroup => oneGroupConditionalSource file
  | .lambda2 => callAt file 28 ⟨range file 6 27, .group ⟨range file 7 26, .group (lambdaAt file 8 "x")⟩⟩
  | .lambda3 => callAt file 30 ⟨range file 6 29, .group ⟨range file 7 28, .group ⟨range file 8 27, .group (lambdaAt file 9 "x")⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .immediate, ⟨cs, .call callee ⟨as, [⟨is, .conditional condition q yes colon no⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 6 10 "flag" condition; let y ← exactLambda? file 13 "x" yes; let n ← exactReference? file 33 41 "ordinary" no
    if h : cs=range file 0 42 ∧ as=range file 5 42 ∧ is=range file 6 41 ∧ q=range file 11 12 ∧ colon=range file 31 32 then some ⟨by rw [c.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .oneGroup, ⟨cs, .call callee ⟨as, [⟨gs, .group ⟨is, .conditional condition q yes colon no⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 7 11 "flag" condition; let y ← exactLambda? file 14 "x" yes; let n ← exactReference? file 34 42 "ordinary" no
    if h : cs=range file 0 44 ∧ as=range file 5 44 ∧ gs=range file 6 43 ∧ is=range file 7 42 ∧ q=range file 12 13 ∧ colon=range file 32 33 then some ⟨by rw [c.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda2, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group body⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let b ← exactLambda? file 8 "x" body
    if h : cs=range file 0 28 ∧ as=range file 5 28 ∧ o=range file 6 27 ∧ i=range file 7 26 then some ⟨by rw [c.down,b.down]; rcases h with ⟨rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda3, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group ⟨j, .group body⟩⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let b ← exactLambda? file 9 "x" body
    if h : cs=range file 0 30 ∧ as=range file 5 30 ∧ o=range file 6 29 ∧ i=range file 7 28 ∧ j=range file 8 27 then some ⟨by rw [c.down,b.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0329-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    wrapped == child && child == some (core mode, .word)) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_two_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance
  proof (wrapperE file mode).provenance
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0329-{label}.sol" text
  let child := elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_twoLevelGroupedConditional
        (types := types) (owner := owner) (inputs := inputs) boundary
      proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("condition-missing", "apply(((missing ? lam(x){return x;} : ordinary)))"),
      ("header", "apply(((flag ? lam(x,y){return x;} : ordinary)))"),
      ("body", "apply(((flag ? lam(x){return flag;} : ordinary)))"),
      ("other-type", "apply(((flag ? lam(x){return x;} : wrong)))"),
      ("other-missing", "apply(((flag ? lam(x){return x;} : missing)))"),
      ("nonfunction", "flag(((flag ? lam(x){return x;} : ordinary)))"),
      ("callee-missing", "globalApply(((flag ? lam(x){return x;} : ordinary)))"),
      ("mixed-grouped", "apply(((flag ? lam(x){return x;} : (lam(y){return y;}))))"),
      ("mixed-nested", "apply(((flag ? lam(x){return x;} : ordinary(lam(y){return y;}))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0329-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0327 Option changed"
  if boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : previous = expected then
      proof (falseRoute (t := types) (o := owner) (i := inputs) boundary)
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact)
    else throw (IO.userError s!"{label}: ADR0327 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) (some .oneGroup)
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) (some .immediate)
  preserved "all-ordinary" "apply(((flag ? ordinary : ordinary)))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 2 then some .lambda2 else if depth = 3 then some .lambda3 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("three-group-conditional", "apply((((flag ? lam(x){return x;} : ordinary))))"),
      ("grouped-only", "apply(((flag ? (lam(x){return x;}) : ordinary)))"),
      ("nested-only", "apply(((flag ? ordinary(lam(x){return x;}) : ordinary)))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply(((lam(x){return lam(y){return y;};})))"), ("inferred-let-lambda", "apply(((lam(x){let y = lam(z){return z;};return x;})))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_two_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_two_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    runExact "immediate-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "one-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "direct-lambda-control" 10 11 directCore choice (directE choice)
    runExact "finite-group-lambda-control" 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0329ParsedLocalApplicationWithTwoLevelGroupedConditionalConsumerIndependent
/-! Run every parsed ADR-0329 wrapper check. -/
def Tests.adr0329ParsedLocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0329ParsedLocalApplicationWithTwoLevelGroupedConditionalConsumerIndependent.exercise
  IO.println "ADR0329 parsed local two-level grouped conditional wrapper GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationWithTwoLevelGroupedExpectedLambda
/-! Independent parsed consumer for the exact-depth-two-first application entry. -/

set_option autoImplicit false

namespace Tests.ADR0322ParsedLocalApplicationWithTwoLevelGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedTwoLevelGroupedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 321
private def foreignOwner := declaration 9321
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId :=
  ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell .word⟩,
  ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩,
  ⟨"ordinary", localId owner 29, functionType⟩
], by decide⟩
private def types : TypeNameTable := []

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) :
    Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaBody (file : Syntax.SourceFile) : Syntax.Block :=
  ⟨range file 14 25,
    [⟨range file 15 24, .returnStmt (some (reference file 22 23 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 8 25, .lambda (range file 8 11)
    ⟨range file 11 14,
      [⟨range file 12 13, .inferred ⟨range file 12 13, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def twoLevelSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 28, .call (reference file 0 5 "apply")
    ⟨range file 5 28, [⟨range file 6 27, .group
      ⟨range file 7 26, .group (lambdaArgument file)⟩⟩]⟩⟩

private def expectedCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)

private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem lambdaElaboration (file : Syntax.SourceFile) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaArgument file)
        (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, lambdaBody file, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem twoLevelElaboration (file : Syntax.SourceFile) :
    TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs (twoLevelSource file) expectedCore .word :=
  .application (calleeElaboration file) (lambdaElaboration file)
private theorem selectedElaboration (file : Syntax.SourceFile) :
    LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
      types owner inputs (twoLevelSource file) expectedCore .word :=
  .twoLevel rfl (twoLevelElaboration file)

/-- The exact parsed source independently constructs, selects and types its evidence. -/
theorem parsed_two_level_static_contract (file : Syntax.SourceFile) :
    LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
        types owner inputs (twoLevelSource file) expectedCore .word ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs (twoLevelSource file) = some (expectedCore, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs (twoLevelSource file) =
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs (twoLevelSource file) ∧
    Core.HasType inputs.context.values expectedCore .word := by
  have evidence := selectedElaboration file
  exact ⟨evidence,
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr evidence,
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_twoLevel rfl,
    evidence.core_hasType⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- Both erased source groups preserve the independently executed Core endpoint. -/
theorem independently_executed_two_level_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      expectedCore (.word seven) initialStore := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd &&
      parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")

private def isExactTwoLevelLambdaApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩⟩]⟩⟩ => true
  | _ => false

private def rejected (label text : String) (recognized : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0322-{label}.sol" text
  check (isExactTwoLevelLambdaApplication parsed == recognized &&
    isTwoLevelGroupedExpectedLambdaArgumentApplication parsed == recognized)
    s!"{label}: exact source-shape boundary changed"
  if recognized then
    check (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs parsed ==
        elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed) s!"{label}: exact-two branch changed"
  else
    check (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs parsed ==
        elaborateLocalApplicationWithGroupedExpectedLambda?
          types owner inputs parsed) s!"{label}: existing branch changed"
  check (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
    types owner inputs parsed).isNone s!"{label}: unified entry unexpectedly accepted"

private def verifyExactParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0322-two-level.sol"
    "apply(((lam(x){return x;})))"
  match shape : parsed with
  | ⟨callSpan, .call ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨outerSpan, .group ⟨innerSpan, .group
        ⟨lambdaSpan, .lambda keywordSpan
          ⟨parametersSpan, [⟨parameterSpan,
            .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
          ⟨bodySpan, [⟨statementSpan, .returnStmt
            (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 28 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 28 ∧
        outerSpan = range file 6 27 ∧ innerSpan = range file 7 26 ∧
        lambdaSpan = range file 8 25 ∧ keywordSpan = range file 8 11 ∧
        parametersSpan = range file 11 14 ∧ parameterSpan = range file 12 13 ∧
        parameterNameSpan = range file 12 13 ∧ bodySpan = range file 14 25 ∧
        statementSpan = range file 15 24 ∧ resultSpan = range file 22 23 ∧
        resultNameSpan = range file 22 23 then
      have parsedEq : parsed = twoLevelSource file := by
        rcases spans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (isExactTwoLevelLambdaApplication parsed &&
        isTwoLevelGroupedExpectedLambdaArgumentApplication parsed &&
        (elaborateLocalApplicationWithGroupedExpectedLambda?
          types owner inputs parsed).isNone &&
        elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs parsed ==
            elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
              types owner inputs parsed &&
        elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs parsed == some (expectedCore, .word))
        "two-level: exact checker result changed"
      proof (show elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs parsed = some (expectedCore, .word) from by
        rw [parsedEq]
        exact elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr
          (selectedElaboration file))
      proof (selectedElaboration file).provenance
      pure file
    else throw (IO.userError "two-level: exact nested spans differ")
  | _ => throw (IO.userError "two-level: exact parsed AST differs")

private def verifyPreservedPaths : IO Unit := do
  for (label, text) in [
      ("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))")] do
    let (_, parsed) ← parseComplete s!"adr0322-{label}.sol" text
    check (!isTwoLevelGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed ==
          elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word)) s!"{label}: path changed"
  for (label, text) in [
      ("ordinary-0", "apply(ordinary)"), ("ordinary-1", "apply((ordinary))"),
      ("ordinary-2", "apply(((ordinary)))"),
      ("ordinary-3", "apply((((ordinary))))")] do
    let (_, parsed) ← parseComplete s!"adr0322-{label}.sol" text
    check (!isTwoLevelGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed ==
          elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (ordinaryCore, .word)) s!"{label}: path changed"
  let (_, deeperLambda) ← parseComplete "adr0322-three-groups.sol"
    "apply((((lam(x){return x;}))))"
  check (!isTwoLevelGroupedExpectedLambdaArgumentApplication deeperLambda &&
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs deeperLambda ==
        elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs deeperLambda &&
    (elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs deeperLambda).isNone) "three-groups: boundary changed"

private def exercise : IO Unit := do
  let file ← verifyExactParse
  proof (parsed_two_level_static_contract file)
  verifyPreservedPaths
  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_two_level_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "bad-header" "apply(((lam(x,y){return x;})))" true
  rejected "bad-body" "apply(((lam(x){return flag;})))" true
  rejected "nonfunction" "flag(((lam(x){return x;})))" true
  rejected "unresolved" "missing(((lam(x){return x;})))" true
  rejected "nested" "ordinary(apply(((lam(x){return x;}))))"
  rejected "tuple" "apply((((lam(x){return x;},ordinary))))"
  rejected "conditional" "apply(((flag ? lam(x){return x;} : ordinary)))"
  rejected "call" "apply(((ordinary(lam(x){return x;}))))"
  rejected "zero" "apply()"
  rejected "multi" "apply(((lam(x){return x;})),ordinary)"
  rejected "top" "((lam(x){return x;}))"
  rejected "return" "apply(((lam(x){return lam(y){return y;};})))" true
  rejected "inferred-let"
    "apply(((lam(x){let y = lam(z){return z;};return x;})))" true

end Tests.ADR0322ParsedLocalApplicationWithTwoLevelGroupedExpectedLambdaConsumerIndependent

def Tests.adr0322ParsedLocalApplicationWithTwoLevelGroupedExpectedLambdaTests : IO Unit := do
  ADR0322ParsedLocalApplicationWithTwoLevelGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0322 parsed two-level-group-first application consumer GREEN"
end
