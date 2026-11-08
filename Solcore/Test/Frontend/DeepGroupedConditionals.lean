import Solcore.Frontend.Fragments.Internal.ExpectedLambdas
import Solcore.Frontend.Fragments.Internal.LocalApplication
import Solcore.Core.Machine
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Core.Eval

/-!
# Deep grouped conditional tests

Expected lambda arguments under grouped conditionals of four to seven levels, and finite groups of three
or more.
-/

section
-- leanmerge: from Solcore.Test.FrontendFiveLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact five-whole-group conditional adapter. -/
set_option autoImplicit false
namespace Tests.ADR0334FiveLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FiveGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 334
private def foreignOwner := declaration 9334
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
private def file : Syntax.SourceId := ⟨.main, "adr0334-symbolic.sol"⟩
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
private def planned (t : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (s : Syntax.Expr) := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ ChildProvenance s c ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ planned types owner inputs s = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ planned types owner inputs s = some (c, .word)
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
  refine ⟨e.classified, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, latest, latest.trans (current.trans (previous.trans oldNone)), by simp [planned, e.classified], by simp [planned, e.classified, elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e]⟩
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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, by simp [planned, h.1], by simp [planned, h.1, h.2]⟩
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
  isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ planned types owner inputs item.1 = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ planned types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route : planned types owner inputs source = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source := by simp [planned, boundary]
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); exact ⟨child, child.provenance⟩
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
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [planned, eLO.classified] using elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLO | simpa [planned, eOL.classified] using elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eOL | simpa [planned, eLL.classified] using elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLL | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2) ∧
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
private def InheritedFailure (source : Syntax.Expr) : Prop := isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ planned types owner inputs source = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ planned types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, by simp [planned, boundary], by simp [planned, boundary, current]⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousFourConditionalCurrentNone
  · exact inherit ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousThreeConditionalCurrentNone)
  · exact inherit ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone))
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)
/-! Selected failures are final; every false neighbor retains the complete ADR-0333 Option. -/
theorem selected_failures_and_complete_adr0333_options_are_exact :
    (∀ source ∈ selectedFailures, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → planned t o i s = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, by intros; simp_all [planned]⟩
end Tests.ADR0334FiveLevelGroupedConditionalSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendFourLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact four-whole-group conditional adapter. -/
set_option autoImplicit false

namespace Tests.ADR0332FourLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FourGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 332
private def foreignOwner := declaration 9332
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
private def file : Syntax.SourceId := ⟨.main, "adr0332-symbolic.sol"⟩
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
private def planned (t : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (s : Syntax.Expr) := if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ ChildProvenance s c ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ planned types owner inputs s = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ planned types owner inputs s = some (c, .word)
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
  refine ⟨e.classified, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, current, current.trans (previous.trans oldNone), by simp [planned, e.classified], by simp [planned, e.classified, elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e]⟩

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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, by simp [planned, h.1], by simp [planned, h.1, h.2]⟩

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
  isFourLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ planned types owner inputs item.1 = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ planned types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route : planned types owner inputs source = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source := by simp [planned, boundary]
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); exact ⟨child, child.provenance⟩
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
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [planned, eLO.classified] using elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLO | simpa [planned, eOL.classified] using elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eOL | simpa [planned, eLL.classified] using elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLL | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2) ∧
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
private def InheritedFailure (source : Syntax.Expr) : Prop := isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ planned types owner inputs source = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ planned types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, by simp [planned, boundary], by simp [planned, boundary, current]⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousThreeConditionalCurrentNone
  · exact inherit ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing (by rfl)).trans previousTwoConditionalCurrentNone)
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)

/-! Selected failures are final; every false neighbor retains the complete ADR-0331 Option. -/
theorem selected_failures_and_complete_adr0331_options_are_exact :
    (∀ source ∈ selectedFailures, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → planned t o i s = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, by intros; simp_all [planned]⟩

end Tests.ADR0332FourLevelGroupedConditionalSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendParsedFiveLevelGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false
namespace Tests.ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedFiveGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 334
private def foreignOwner := declaration 9334
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
theorem parsed_five_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; rcases oldBoundaries file mode with ⟨four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  exact ⟨child, child.classified, four, three, two, one, immediate, generic,
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    route, child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_five_group_conditional_core (mode : Mode) (choice : Bool)
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
  let (file, parsed) ← parseComplete s!"adr0334-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_five_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0334-{label}.sol" text
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
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
  let (file, parsed) ← parseComplete s!"adr0334-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0333 Option changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
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
        have evaluated := independently_executed_five_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_five_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent
def Tests.adr0334ParsedFiveLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0334 parsed five-level grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedFourLevelGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false
namespace Tests.ADR0332ParsedFourLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedFourGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 332
private def foreignOwner := declaration 9332
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
theorem parsed_four_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have old := oldBoundaries file mode
  exact ⟨child, child.classified, old.1, old.2.1, old.2.2.1, old.2.2.2.1, old.2.2.2.2,
    elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing old.1,
    child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_four_group_conditional_core (mode : Mode) (choice : Bool)
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
  let (file, parsed) ← parseComplete s!"adr0332-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_four_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0332-{label}.sol" text
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
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
  let (file, parsed) ← parseComplete s!"adr0332-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateFourLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0331 Option changed"
  if boundary : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
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
        have evaluated := independently_executed_four_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_four_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0332ParsedFourLevelGroupedConditionalConsumerIndependent
def Tests.adr0332ParsedFourLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0332ParsedFourLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0332 parsed four-level grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSevenLevelGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false
namespace Tests.ADR0338ParsedSevenLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedSevenGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 338
private def foreignOwner := declaration 9338
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
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_seven_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; rcases oldBoundaries file mode with ⟨six, five, four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) six
  exact ⟨child, child.classified, six, five, four, three, two, one, immediate, generic,
    elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    route, child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_seven_group_conditional_core (mode : Mode) (choice : Bool)
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
  let (file, parsed) ← parseComplete s!"adr0338-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_seven_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0338-{label}.sol" text
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
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
  let (file, parsed) ← parseComplete s!"adr0338-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0337 Option changed"
  if boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
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
        have evaluated := independently_executed_seven_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_seven_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional", "five-group-conditional", "six-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups", "seven-lambda-groups", "eight-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0338ParsedSevenLevelGroupedConditionalConsumerIndependent
def Tests.adr0338ParsedSevenLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0338ParsedSevenLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0338 parsed seven-level grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedSixLevelGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false
namespace Tests.ADR0336ParsedSixLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedSixGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 336
private def foreignOwner := declaration 9336
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
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_six_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isSixLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; rcases oldBoundaries file mode with ⟨five, four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) five
  exact ⟨child, child.classified, five, four, three, two, one, immediate, generic,
    elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    route, child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_six_group_conditional_core (mode : Mode) (choice : Bool)
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
  let (file, parsed) ← parseComplete s!"adr0336-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_six_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0336-{label}.sol" text
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
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
  let (file, parsed) ← parseComplete s!"adr0336-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0335 Option changed"
  if boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
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
        have evaluated := independently_executed_six_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_six_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional", "five-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups", "seven-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0336ParsedSixLevelGroupedConditionalConsumerIndependent
def Tests.adr0336ParsedSixLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0336ParsedSixLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0336 parsed six-level grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedThreeOrMoreGroupedExpectedLambdaArgumentApplication
/-! Independent parsed consumer for the finite three-or-more group lambda adapter. -/

set_option autoImplicit false

namespace Tests.ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedThreeOrMoreGroupedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 323
private def foreignOwner := declaration 9323
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
  ⟨range file 15 26,
    [⟨range file 16 25, .returnStmt (some (reference file 23 24 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 9 26, .lambda (range file 9 12)
    ⟨range file 12 15,
      [⟨range file 13 14, .inferred ⟨range file 13 14, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def threeGrouped (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 29, .group ⟨range file 7 28, .group
    ⟨range file 8 27, .group (lambdaArgument file)⟩⟩⟩
private def threeLevelSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 30, .call (reference file 0 5 "apply")
    ⟨range file 5 30, [threeGrouped file]⟩⟩

private def expectedCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

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

private theorem threeSpine (file : Syntax.SourceFile) :
    DirectLambdaGroupSpine (threeGrouped file)
      [range file 6 29, range file 7 28, range file 8 27] (lambdaArgument file) :=
  .group (.group (.group .lambda))

private theorem threeLevelElaboration (file : Syntax.SourceFile) :
    ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs (threeLevelSource file) expectedCore .word :=
  .application (threeSpine file) (calleeElaboration file) (lambdaElaboration file)

/-- The exact parsed source retains its ordered spans, checks, classifies and types. -/
theorem parsed_three_or_more_static_contract (file : Syntax.SourceFile) :
    DirectLambdaGroupSpine (threeGrouped file)
        [range file 6 29, range file 7 28, range file 8 27] (lambdaArgument file) ∧
    ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs (threeLevelSource file) expectedCore .word ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs (threeLevelSource file) = some (expectedCore, .word) ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (threeLevelSource file) = true ∧
    Core.HasType inputs.context.values expectedCore .word := by
  have evidence := threeLevelElaboration file
  exact ⟨threeSpine file, evidence,
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr evidence,
    evidence.classified, evidence.core_hasType⟩

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

/-- Erasing every finite source group preserves the independently executed Core endpoint. -/
theorem independently_executed_three_or_more_core_application
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

private def peelObservedGroup? : Option (Syntax.Expr × List Syntax.SourceSpan) →
    Option (Syntax.Expr × List Syntax.SourceSpan)
  | some (⟨span, .group inner⟩, reversed) => some (inner, span :: reversed)
  | _ => none

private def directLambdaGroupSpans? (depth : Nat) (source : Syntax.Expr) :
    Option (List Syntax.SourceSpan) :=
  let state := Nat.rec (motive := fun _ => Option (Syntax.Expr × List Syntax.SourceSpan))
    (some (source, [])) (fun _ state => peelObservedGroup? state) depth
  match state with
  | some (⟨_, .lambda _ _ _ _⟩, reversed) => some reversed.reverse
  | _ => none

private def applicationGroupSpans? (depth : Nat) : Syntax.Expr → Option (List Syntax.SourceSpan)
  | ⟨_, .call _ ⟨_, [grouped]⟩⟩ => directLambdaGroupSpans? depth grouped
  | _ => none

private def rejected (label text : String) (recognized : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0323-{label}.sol" text
  check (isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == recognized)
    s!"{label}: finite-spine source-shape boundary changed"
  check (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
    types owner inputs parsed).isNone s!"{label}: finite-spine adapter unexpectedly accepted"

private def verifyExactParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0323-three-level.sol"
    "apply((((lam(x){return x;}))))"
  match shape : parsed with
  | ⟨callSpan, .call ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨firstSpan, .group ⟨secondSpan, .group
        ⟨thirdSpan, .group ⟨lambdaSpan, .lambda keywordSpan
          ⟨parametersSpan, [⟨parameterSpan,
            .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
          ⟨bodySpan, [⟨statementSpan, .returnStmt
            (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩⟩⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 30 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 30 ∧
        firstSpan = range file 6 29 ∧ secondSpan = range file 7 28 ∧
        thirdSpan = range file 8 27 ∧ lambdaSpan = range file 9 26 ∧
        keywordSpan = range file 9 12 ∧ parametersSpan = range file 12 15 ∧
        parameterSpan = range file 13 14 ∧ parameterNameSpan = range file 13 14 ∧
        bodySpan = range file 15 26 ∧ statementSpan = range file 16 25 ∧
        resultSpan = range file 23 24 ∧ resultNameSpan = range file 23 24 then
      have parsedEq : parsed = threeLevelSource file := by
        rcases spans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
        elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed == some (expectedCore, .word))
        "three-level: exact checker result changed"
      proof (show elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed = some (expectedCore, .word) from by
        rw [parsedEq]
        exact elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr
          (threeLevelElaboration file))
      proof (threeLevelElaboration file).provenance
      pure file
    else throw (IO.userError "three-level: exact nested spans differ")
  | _ => throw (IO.userError "three-level: exact parsed AST differs")

private def verifyDeeperSpine (label text : String) (depth : Nat) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0323-{label}.sol" text
  let total := 24 + 2 * depth
  let expectedSpans := (List.range depth).map fun index =>
    range file (6 + index) (total - 1 - index)
  check (applicationGroupSpans? depth parsed == some expectedSpans &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (expectedCore, .word))
    s!"{label}: ordered finite-spine checker result changed"

private def verifyDeeperSpines : IO Unit := do
  verifyDeeperSpine "four-groups" "apply(((((lam(x){return x;})))))" 4
  verifyDeeperSpine "seven-groups" "apply((((((((lam(x){return x;}))))))))" 7

private def verifyShallowControls : IO Unit := do
  for (label, text) in [
      ("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))")] do
    let (_, parsed) ← parseComplete s!"adr0323-{label}.sol" text
    check (!isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
      (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs parsed).isNone &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word) &&
      elaborateLocalApplicationWithGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word)) s!"{label}: path changed"
  let (_, parsed) ← parseComplete "adr0323-two-groups.sol"
    "apply(((lam(x){return x;})))"
  check (!isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs parsed == some (expectedCore, .word) &&
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (expectedCore, .word)) "two-groups: path changed"

private def exercise : IO Unit := do
  let file ← verifyExactParse
  proof (parsed_three_or_more_static_contract file)
  verifyDeeperSpines
  verifyShallowControls
  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_three_or_more_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "bad-header" "apply((((lam(x,y){return x;}))))" true
  rejected "bad-body" "apply((((lam(x){return flag;}))))" true
  rejected "nonfunction" "flag((((lam(x){return x;}))))" true
  rejected "unresolved" "missing((((lam(x){return x;}))))" true
  rejected "return" "apply((((lam(x){return lam(y){return y;};}))))" true
  rejected "inferred-let"
    "apply((((lam(x){let y = lam(z){return z;};return x;}))))" true
  rejected "non-lambda" "apply((((ordinary))))"
  rejected "nested" "ordinary(apply((((lam(x){return x;})))))"
  rejected "tuple" "apply(((((lam(x){return x;},ordinary)))))"
  rejected "conditional" "apply((((flag ? lam(x){return x;} : ordinary))))"
  rejected "call" "apply((((ordinary(lam(x){return x;})))))"
  rejected "zero" "apply()"
  rejected "multi" "apply((((lam(x){return x;}))),ordinary)"
  rejected "top" "(((lam(x){return x;})))"

end Tests.ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent

def Tests.adr0323ParsedThreeOrMoreGroupedExpectedLambdaTests : IO Unit := do
  ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0323 parsed three-or-more grouped expected-lambda consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendSevenLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact seven-whole-group conditional adapter. -/
set_option autoImplicit false
namespace Tests.ADR0338SevenLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"SevenGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 338
private def foreignOwner := declaration 9338
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
private def file : Syntax.SourceId := ⟨.main, "adr0338-symbolic.sol"⟩
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
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent]
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
private def planned (t : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (s : Syntax.Expr) := if isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan terminalGroupSpan seventhGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨terminalGroupSpan, .group ⟨seventhGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ ChildProvenance s c ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ planned types owner inputs s = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ planned types owner inputs s = some (c, .word)
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group innermost => cases innermost with | group final => cases final with | group terminal => cases terminal with | group seventh => cases seventh
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
  refine ⟨e.classified, six, five, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, wrapper, wrapper.trans (complete.trans (latest.trans (current.trans (previous.trans oldNone)))), by simp [planned, e.classified], by simp [planned, e.classified, elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e]⟩
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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, by simp [planned, h.1], by simp [planned, h.1, h.2]⟩
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
  isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ planned types owner inputs item.1 = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ planned types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithSixLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route : planned types owner inputs source = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source := by simp [planned, boundary]
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); exact ⟨child, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl immediateE) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl oneGroupE rfl)) | exact completeOption (completeFallback (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE))) | exact completeOption (completeFallback currentThreeCheck) | exact completeOption (completeFallback currentFourCheck) | exact completeOption (completeFallback currentFiveCheck) | exact completeOption currentSixCheck | exact completeOption eightGroupCurrentNone | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl)) | exact completeOption groupedCurrentNone | exact completeOption nestedCurrentNone | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda0E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda1E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda2E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda3E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda4E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda5E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda6E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda7E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl lambda8E) rfl)) | exact completeOption (completeFallback (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl)) | exact completeOption (completeFallback rfl)
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (sixGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834], some (expectedCore, .word)), (lambdaApplication 855 [858, 859, 860, 861, 862, 863, 864, 865], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [planned, eLO.classified] using elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLO | simpa [planned, eOL.classified] using elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eOL | simpa [planned, eLL.classified] using elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLL | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2) ∧
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
private def InheritedFailure (source : Syntax.Expr) : Prop := isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ planned types owner inputs source = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ planned types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, by simp [planned, boundary], by simp [planned, boundary, current]⟩
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
    (∀ source ∈ selectedFailures, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateSevenLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isSevenLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → planned t o i s = elaborateLocalApplicationWithSixLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, by intros; simp_all [planned]⟩
end Tests.ADR0338SevenLevelGroupedConditionalSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendSixLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact six-whole-group conditional adapter. -/
set_option autoImplicit false
namespace Tests.ADR0336SixLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"SixGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 336
private def foreignOwner := declaration 9336
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
private def file : Syntax.SourceId := ⟨.main, "adr0336-symbolic.sol"⟩
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
private theorem missingC (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, absent]
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
private def planned (t : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (s : Syntax.Expr) := if isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan deepestGroupSpan innermostGroupSpan terminalGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨deepestGroupSpan, .group ⟨innermostGroupSpan, .group ⟨terminalGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isFourLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ SixLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ ChildProvenance s c ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ planned types owner inputs s = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ planned types owner inputs s = some (c, .word)
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild with | group deepest => cases deepest with | group innermost => cases innermost with | group final => cases final with | group terminal => cases terminal
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
  have latest := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  have complete := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) five
  refine ⟨e.classified, five, four, three, two, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, complete, complete.trans (latest.trans (current.trans (previous.trans oldNone))), by simp [planned, e.classified], by simp [planned, e.classified, elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e]⟩
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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, by simp [planned, h.1], by simp [planned, h.1, h.2]⟩
private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def twoGroupControl := selectedAt 520 [525, 526] (lambda 530 "x") (ref 550 "ordinary")
private def threeGroupControl := selectedAt 720 [725, 726, 727] (lambda 730 "x") (ref 750 "ordinary")
private def fourGroupControl := selectedAt 750 [755, 756, 757, 758] (lambda 760 "x") (ref 780 "ordinary")
private def fiveGroupControl := selectedAt 1300 [1305, 1306, 1307, 1308, 1309] (lambda 1320 "x") (ref 1340 "ordinary")
private theorem immediateE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word := .conditional rfl (.application rfl (applyE 541) (flagE 542) (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word := .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582) (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem twoGroupE : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs twoGroupControl coreLO .word := .application rfl (applyE 521) (flagE 522) (.expected rfl (lambdaE 530 "x")) (.ordinary rfl (ordinaryE 550))
private theorem threeGroupE : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs threeGroupControl coreLO .word := .application rfl (applyE 721) (flagE 722) (.expected rfl (lambdaE 730 "x")) (.ordinary rfl (ordinaryE 750))
private theorem fourGroupE : FourLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fourGroupControl coreLO .word := .application rfl (applyE 751) (flagE 752) (.expected rfl (lambdaE 760 "x")) (.ordinary rfl (ordinaryE 780))
private theorem fiveGroupE : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs fiveGroupControl coreLO .word := .application rfl (applyE 1301) (flagE 1302) (.expected rfl (lambdaE 1320 "x")) (.ordinary rfl (ordinaryE 1340))
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
private theorem currentCheck {source core} (e : LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing five (.existing four (.existing three e)))
private theorem currentOldCheck {source core} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs source core .word) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := currentCheck (.existing boundary e) three four five
private theorem currentOldNone {source : Syntax.Expr} (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (old : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (three : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (four : isFourLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (five : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none := (elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_of_existing five).trans ((elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing four).trans ((elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing three).trans ((elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing boundary).trans old)))
private theorem currentThreeCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs threeGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.existing rfl (.threeLevelGroupedConditional threeGroupE.classified threeGroupE)))
private theorem currentFourCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fourGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.existing rfl (.fourLevelGroupedConditional fourGroupE.classified fourGroupE))
private theorem currentFiveCheck : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs fiveGroupControl = some (coreLO, .word) := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mpr (.fiveLevelGroupedConditional fiveGroupE.classified fiveGroupE)
private def sevenGroupConditional := selectedAt 760 [765, 766, 767, 768, 769, 770, 771] (lambda 780 "x") (ref 800 "ordinary")
private def allOrdinarySource := selectedAt 810 [815, 816, 817, 818, 819, 820] (ref 820 "ordinary") (ref 830 "ordinary")
private def groupedOnlySource := selectedAt 840 [845, 846, 847, 848, 849, 850] (groups [851] (lambda 860 "x")) (ref 880 "ordinary")
private def nestedOnlySource := selectedAt 890 [895, 896, 897, 898, 899, 900] (nestedLambdaCall 901) (ref 920 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word := .existing rfl (noFiniteAt 810 _ _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 811) (.group (.group (.group (.group (.group (.group (.conditional (flagE 812) (ordinaryE 820) (ordinaryE 830))))))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word := .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (sevenGroupConditional, none), (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none), (nestedOnlySource, none), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834], some (expectedCore, .word)), (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none), (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isSixLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ planned types owner inputs item.1 = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ planned types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithFiveLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithFourLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route : planned types owner inputs source = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source := by simp [planned, boundary]
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); exact ⟨child, child.provenance⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact completeOption (currentOldCheck rfl (.existing rfl immediateE) rfl) | exact completeOption (currentOldCheck rfl oneGroupE rfl) | exact completeOption (currentCheck (.twoLevelGroupedConditional twoGroupE.classified twoGroupE)) | exact completeOption currentThreeCheck | exact completeOption currentFourCheck | exact completeOption currentFiveCheck | exact completeOption (currentOldNone rfl (by simpa only [sevenGroupConditional] using oldConditionalNone 760 [765, 766, 767, 768, 769, 770, 771] (lambda 780 "x") (ref 800 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))) | exact completeOption (currentOldCheck rfl (.existing rfl allOrdinaryE) rfl) | exact completeOption (currentOldNone rfl (by simpa only [groupedOnlySource] using oldConditionalNone 840 [845, 846, 847, 848, 849, 850] (groups [851] (lambda 860 "x")) (ref 880 "ordinary") rfl rfl (noFiniteAt 840 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))) | exact completeOption (currentOldNone rfl (by simpa only [nestedOnlySource] using oldConditionalNone 890 [895, 896, 897, 898, 899, 900] (nestedLambdaCall 901) (ref 920 "ordinary") rfl rfl (noFiniteAt 890 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))) | exact completeOption (currentOldCheck rfl (.existing rfl lambda0E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda1E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda2E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda3E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda4E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda5E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda6E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl lambda7E) rfl) | exact completeOption (currentOldCheck rfl (.existing rfl ordinaryApplicationE) rfl) | exact completeOption rfl
private def runtimeSelections : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) := [(cLO, some (coreLO, .word)), (cOL, some (coreOL, .word)), (cLL, some (coreLL, .word)), (immediateControl, some (coreLO, .word)), (oneGroupControl, some (coreLO, .word)), (twoGroupControl, some (coreLO, .word)), (threeGroupControl, some (coreLO, .word)), (fourGroupControl, some (coreLO, .word)), (fiveGroupControl, some (coreLO, .word)), (lambdaApplication 620 [], some (expectedCore, .word)), (lambdaApplication 650 [653], some (expectedCore, .word)), (lambdaApplication 680 [683, 684], some (expectedCore, .word)), (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)), (lambdaApplication 740 [743, 744, 745, 746], some (expectedCore, .word)), (lambdaApplication 770 [773, 774, 775, 776, 777], some (expectedCore, .word)), (lambdaApplication 795 [798, 799, 800, 801, 802, 803], some (expectedCore, .word)), (lambdaApplication 825 [828, 829, 830, 831, 832, 833, 834], some (expectedCore, .word))]
private theorem runtimeSelectionsExact : ∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2 := by
  intro item member; simp only [runtimeSelections, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [planned, eLO.classified] using elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLO | simpa [planned, eOL.classified] using elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eOL | simpa [planned, eLL.classified] using elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr eLL | exact (completeOptionsExact _ (by simp [completeNeighbors])).2.2.2.2.1
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ item ∈ runtimeSelections, planned types owner inputs item.1 = item.2) ∧
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
private def InheritedFailure (source : Syntax.Expr) : Prop := isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ planned types owner inputs source = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ planned types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, by simp [planned, boundary], by simp [planned, boundary, current]⟩
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
    (∀ source ∈ selectedFailures, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateSixLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isSixLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → planned t o i s = elaborateLocalApplicationWithFiveLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, by intros; simp_all [planned]⟩
end Tests.ADR0336SixLevelGroupedConditionalSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendThreeOrMoreGroupedExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the finite three-or-more group adapter. -/
set_option autoImplicit false
namespace Tests.ADR0323SymbolicThreeOrMoreGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ThreeOrMoreGroupedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 323
private def foreignOwner := declaration 9323
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
private def file : Syntax.SourceId := ⟨.main, "three-or-more-grouped-lambda.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (positions : List Nat) (source : Syntax.Expr) : Syntax.Expr := positions.foldr (fun n inner => ⟨span n, .group inner⟩) source
private def callAt (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body : Syntax.Block := ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr := ⟨span 4, .lambda (span 5) ⟨span 6, [⟨span 6, .inferred ⟨span 6, "x"⟩⟩]⟩ none body⟩
private def source (positions : List Nat) : Syntax.Expr := callAt 0 (ref 10 "apply") (groups positions argument)
private def core : Core.Expr := .apply (.var 0) (.lambda .word .word (.var 0))
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem lambdaElaboration : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs argument (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner "x" .word, body, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem groupsSpine {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal) (positions : List Nat) :
    DirectLambdaGroupSpine (groups positions terminal) (positions.map span) terminal := by
  induction positions with | nil => exact base | cons head tail ih => exact .group ih
private theorem groupSpine (positions : List Nat) : DirectLambdaGroupSpine (groups positions argument) (positions.map span) argument := groupsSpine .lambda positions
private theorem groupSpine_unique {source firstTerminal secondTerminal : Syntax.Expr} {firstSpans secondSpans : List Syntax.SourceSpan}
    (first : DirectLambdaGroupSpine source firstSpans firstTerminal) (second : DirectLambdaGroupSpine source secondSpans secondTerminal) :
    firstSpans = secondSpans ∧ firstTerminal = secondTerminal := by
  induction first generalizing secondSpans secondTerminal with
  | lambda => cases second; exact ⟨rfl, rfl⟩
  | group child ih => cases second with | group other => obtain ⟨rfl, rfl⟩ := ih other; exact ⟨rfl, rfl⟩
private theorem selectedEvidence (first second third : Nat) (rest : List Nat) : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
      (source (first :: second :: third :: rest)) core .word :=
  .application (groupSpine _) (applyElaboration 10) lambdaElaboration
private def deepPositions : List Nat := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
/-- Every finite qualifying spine retains exact ordered provenance and one Core result. -/
theorem every_finite_group_spine_has_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    (∀ first second third rest, DirectLambdaGroupSpine (groups (first :: second :: third :: rest) argument) ((first :: second :: third :: rest).map span) argument ∧
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (source (first :: second :: third :: rest)) core .word ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source (first :: second :: third :: rest)) = true ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (source (first :: second :: third :: rest)) = some (core, .word) ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (source (first :: second :: third :: rest)) ≠ none ∧ Core.HasType inputs.context.values core .word ∧
      ∃ callSpan argumentsSpan firstSpan secondSpan thirdSpan restSpans callee grouped terminal functionCore argumentCore parameterType,
        source (first :: second :: third :: rest) = ⟨callSpan, .call callee ⟨argumentsSpan, [grouped]⟩⟩ ∧
        DirectLambdaGroupSpine grouped (firstSpan :: secondSpan :: thirdSpan :: restSpans) terminal ∧
        RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧
        ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs terminal argumentCore parameterType ∧ core = .apply functionCore argumentCore) ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source deepPositions) = true ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (source deepPositions) = some (core, .word) := by
  change (["apply", "opaque", "apply", "flag", "ordinary"].zip [applyId, opaqueId, duplicateId, flagId, ordinaryId])[1]?.map Prod.snd = some opaqueId ∧ _
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro first second third rest
    have evidence := selectedEvidence first second third rest
    have checked := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr evidence
    refine ⟨groupSpine _, evidence, evidence.classified, checked, ?_, evidence.core_hasType, evidence.provenance⟩
    intro rejected; rw [rejected] at checked; cases checked
  · exact (selectedEvidence 200 201 202 [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]).classified
  · exact elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr (selectedEvidence 200 201 202 [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215])
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
/-- The shared Core endpoint executes independently and preserves any caller store. -/
theorem independently_executed_finite_group_spine_core (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore core (.word seven) initialStore := by
  exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def directSource := source []
private def oneSource := source [20]
private def twoSource := source [20, 21]
private def threeSource := source [20, 21, 22]
private def fourSource := source [20, 21, 22, 23]
private theorem twoEvidence : TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs twoSource core .word := .application (applyElaboration 10) lambdaElaboration
private theorem directOld : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs directSource core .word := .existing rfl (.expected rfl (.application (applyElaboration 10) lambdaElaboration))
private theorem oneOld : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs oneSource core .word := .grouped rfl (.application (applyElaboration 10) lambdaElaboration)
private theorem oldThreeNone : elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs threeSource = none := by
  rw [elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing (by rfl)]
  rw [elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing (by rfl)]
  change elaborateRecursiveLocalComputation? inputs.names inputs.context threeSource = none
  simp [threeSource, source, callAt, groups, ref, argument, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]
private def badHeader : Syntax.Expr := ⟨span 30, .lambda (span 31) ⟨span 32, []⟩ none body⟩
private def badBody : Syntax.Expr := ⟨span 33, .lambda (span 34)
  ⟨span 35, [⟨span 35, .inferred ⟨span 35, "x"⟩⟩]⟩ none ⟨span 36, [⟨span 37, .returnStmt none⟩]⟩⟩
private def returnedLambda : Syntax.Expr := ⟨span 38, .lambda (span 39)
  ⟨span 40, [⟨span 40, .inferred ⟨span 40, "y"⟩⟩]⟩ none ⟨span 41, [⟨span 42, .returnStmt (some (ref 43 "y"))⟩]⟩⟩
private def returnArgument : Syntax.Expr := ⟨span 44, .lambda (span 45)
  ⟨span 46, [⟨span 46, .inferred ⟨span 46, "x"⟩⟩]⟩ none ⟨span 47, [⟨span 48, .returnStmt (some returnedLambda)⟩]⟩⟩
private def letArgument : Syntax.Expr := ⟨span 49, .lambda (span 50)
  ⟨span 51, [⟨span 51, .inferred ⟨span 51, "x"⟩⟩]⟩ none ⟨span 52,
  [⟨span 53, .letDecl ⟨span 54, "y"⟩ none (some returnedLambda)⟩, ⟨span 55, .returnStmt (some (ref 56 "x"))⟩]⟩⟩
private def recognized (n : Nat) (callee candidate : Syntax.Expr) :=
  callAt n callee (groups [n + 2, n + 3, n + 4] candidate)
private def badHeaderSource := recognized 60 (ref 66 "apply") badHeader
private def badBodySource := recognized 70 (ref 76 "apply") badBody
private def nonFunctionSource := recognized 80 (ref 86 "flag") argument
private def unresolvedSource := recognized 90 (ref 96 "missing") argument
private def returnSource := recognized 100 (ref 106 "apply") returnArgument
private def letSource := recognized 110 (ref 116 "apply") letArgument
private def ordinaryArgument := ref 120 "ordinary"
private def nonLambdaSource := recognized 121 (ref 127 "apply") ordinaryArgument
private def deepOrdinarySource := callAt 130 (ref 132 "apply")
  (groups [140, 141, 142, 143, 144, 145, 146, 147] ordinaryArgument)
private def nestedSource := callAt 150 (ref 152 "ordinary") threeSource
private def tupleSource := recognized 160 (ref 166 "apply") ⟨span 167, .tuple ⟨span 168, [argument, ordinaryArgument]⟩⟩
private def conditionalSource := recognized 170 (ref 176 "apply") ⟨span 177,
  .conditional (ref 178 "flag") (span 180) argument (span 181) ordinaryArgument⟩
private def callSource := recognized 190 (ref 196 "apply") (callAt 197 ordinaryArgument argument)
private def zeroSource : Syntax.Expr := ⟨span 220, .call (ref 222 "apply") ⟨span 221, []⟩⟩
private def multiSource : Syntax.Expr := ⟨span 223, .call (ref 225 "apply")
  ⟨span 224, [groups [226, 227, 228] argument, ordinaryArgument]⟩⟩
private def topSource := groups [230, 231, 232] argument
private theorem expectedAbsent (candidate : Syntax.Expr) (absent : ¬ ∃ c,
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs candidate c functionType) :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs candidate functionType = none :=
  (elaborateExpectedComputationLambda?_eq_none_iff (@elaborateRecursiveLocalComputation?_iff)).mpr absent
private theorem returnAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs returnArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | expression e => cases e with | pure r _ _ => cases r
private theorem letAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs letArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | inferred e _ => cases e with | pure r _ _ => cases r
private theorem recognizedClassified {terminal : Syntax.Expr}
    (base : DirectLambdaGroupSpine terminal [] terminal) (n : Nat) (callee : Syntax.Expr) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (recognized n callee terminal) = true := by
  apply isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mpr
  exact ⟨span (n + 2), span (n + 3), span (n + 4), [], terminal, groupsSpine base _⟩
private theorem rejectedWithExpectedNone {callSpan argumentsSpan first second third : Syntax.SourceSpan}
    {rest : List Syntax.SourceSpan} {callee grouped terminal : Syntax.Expr}
    {functionCore : Core.Expr} {parameterType resultType : Core.Ty}
    (spine : DirectLambdaGroupSpine grouped (first :: second :: third :: rest) terminal)
    (calleeChecked : elaborateRecursiveLocalComputation? inputs.names inputs.context callee =
      some (functionCore, .function parameterType resultType))
    (argumentRejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      types owner inputs terminal parameterType = none) :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs
      ⟨callSpan, .call callee ⟨argumentsSpan, [grouped]⟩⟩ = none := by
  apply elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr
  rintro ⟨_, _, evidence⟩; cases evidence with
  | application otherSpine otherCallee otherArgument =>
    obtain ⟨_, rfl⟩ := groupSpine_unique spine otherSpine
    have c := elaborateRecursiveLocalComputation?_iff.mpr otherCallee
    rw [calleeChecked] at c; cases c
    have a := (elaborateExpectedComputationLambda?_iff (@elaborateRecursiveLocalComputation?_iff)).mpr otherArgument
    rw [argumentRejected] at a; cases a
private theorem applyRejected {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal)
    (n : Nat) (rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      types owner inputs terminal functionType = none) :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs
      (recognized n (ref (n + 6) "apply") terminal) = none :=
  rejectedWithExpectedNone (groupsSpine base _) (elaborateRecursiveLocalComputation?_iff.mpr
    (applyElaboration (n + 6))) rejected
private theorem rejectedWithNoFunctionCallee {callSpan argumentsSpan : Syntax.SourceSpan}
    {callee grouped : Syntax.Expr} (absent : ¬ ∃ f p r,
      RecursiveLocalComputationElaborates inputs.names inputs.context callee f (.function p r)) :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs
      ⟨callSpan, .call callee ⟨argumentsSpan, [grouped]⟩⟩ = none := by
  apply elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr
  rintro ⟨_, _, e⟩; cases e with | application _ c _ => exact absent ⟨_, _, _, c⟩
private theorem recognizedFailures : ∀ candidate ∈
    [badHeaderSource, badBodySource, nonFunctionSource, unresolvedSource, returnSource, letSource],
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = true ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  have bh : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs badHeader functionType = none := by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
  have bb : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs badBody functionType = none := by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBody functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl
  have flagAbsent : ¬ ∃ f p r, RecursiveLocalComputationElaborates inputs.names inputs.context (ref 86 "flag") f (.function p r) := by
    rintro ⟨_, _, _, h⟩; have c := elaborateRecursiveLocalComputation?_iff.mpr h
    rw [elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration 86)] at c; cases c
  have missingAbsent : ¬ ∃ f p r, RecursiveLocalComputationElaborates inputs.names inputs.context (ref 96 "missing") f (.function p r) := by
    rintro ⟨_, _, _, h⟩; have c := elaborateRecursiveLocalComputation?_iff.mpr h
    have none : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref 96 "missing") = none := by
      have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
      simp only [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
        resolveLocalExpression?, absent, Option.map_none, bind, Option.bind_none]
    rw [none] at c; cases c
  intro candidate membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨recognizedClassified .lambda _ _, applyRejected .lambda 60 bh⟩
  · exact ⟨recognizedClassified .lambda _ _, applyRejected .lambda 70 bb⟩
  · exact ⟨recognizedClassified .lambda _ _, by apply rejectedWithNoFunctionCallee; exact flagAbsent⟩
  · exact ⟨recognizedClassified .lambda _ _, by apply rejectedWithNoFunctionCallee; exact missingAbsent⟩
  · exact ⟨recognizedClassified .lambda _ _, applyRejected .lambda 100 (expectedAbsent _ returnAbsent)⟩
  · exact ⟨recognizedClassified .lambda _ _, applyRejected .lambda 110 (expectedAbsent _ letAbsent)⟩
private theorem spineInsideGroups {positions : List Nat} {source terminal : Syntax.Expr}
    {spans : List Syntax.SourceSpan} (h : DirectLambdaGroupSpine (groups positions source) spans terminal) :
    ∃ tailSpans, DirectLambdaGroupSpine source tailSpans terminal := by
  induction positions generalizing spans with
  | nil => exact ⟨spans, h⟩
  | cons head tail ih => cases h with | group child => exact ih child
private theorem unclassified {grouped : Syntax.Expr}
    (absent : ¬ ∃ spans terminal, DirectLambdaGroupSpine grouped spans terminal)
    (n : Nat) (callee : Syntax.Expr) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (callAt n callee grouped) = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  exact absent ⟨_, _, spine⟩
private theorem rejectedIfUnclassified {candidate : Syntax.Expr}
    (h : isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = false) :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  apply elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mpr
  rintro ⟨_, _, e⟩; have selected := e.classified; rw [h] at selected; cases selected
private theorem shallowUnclassified (positions : List Nat) (small : positions.length < 3) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source positions) = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  obtain ⟨_, _, _, rest, _, other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  have lengths := congrArg List.length (groupSpine_unique (groupSpine positions) other).1
  simp at lengths
  omega
private theorem shallowPaths : ∀ candidate ∈ [directSource, oneSource, twoSource],
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = false ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  intro candidate membership; simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · have h := shallowUnclassified [] (by decide); exact ⟨h, rejectedIfUnclassified h⟩
  · have h := shallowUnclassified [20] (by decide); exact ⟨h, rejectedIfUnclassified h⟩
  · have h := shallowUnclassified [20, 21] (by decide); exact ⟨h, rejectedIfUnclassified h⟩
private theorem falseShapes : ∀ candidate ∈
    [nonLambdaSource, deepOrdinarySource, nestedSource, tupleSource, conditionalSource,
      callSource, zeroSource, multiSource, topSource],
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = false ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  have atomic (s : Syntax.Expr) (h : ¬ ∃ spans terminal, DirectLambdaGroupSpine s spans terminal)
      (positions : List Nat) : ¬ ∃ spans terminal, DirectLambdaGroupSpine (groups positions s) spans terminal := by
    rintro ⟨_, _, spine⟩; obtain ⟨_, child⟩ := spineInsideGroups spine; exact h ⟨_, _, child⟩
  have ordinary : ¬ ∃ spans terminal, DirectLambdaGroupSpine ordinaryArgument spans terminal := by
    rintro ⟨_, _, h⟩; cases h
  have finish {s : Syntax.Expr} (h : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) :
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs s = none :=
    ⟨h, rejectedIfUnclassified h⟩
  intro candidate membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply finish; apply unclassified; exact atomic _ ordinary _
  · apply finish; apply unclassified; exact atomic _ ordinary _
  · apply finish; apply unclassified; rintro ⟨_, _, e⟩; cases e
  · apply finish; apply unclassified; apply atomic; rintro ⟨_, _, e⟩; cases e
  · apply finish; apply unclassified; apply atomic; rintro ⟨_, _, e⟩; cases e
  · apply finish; apply unclassified; apply atomic; rintro ⟨_, _, e⟩; cases e
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
/-- Shallow frozen paths and every selected or structural rejection stay exact. -/
theorem minimum_depth_failures_and_old_paths_are_exact :
    (∀ candidate ∈ [directSource, oneSource, twoSource],
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = false ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs twoSource = some (core, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs directSource = some (core, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs oneSource = some (core, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs twoSource = some (core, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs threeSource = none ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs threeSource = some (core, .word) ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs fourSource = some (core, .word) ∧
    (∀ candidate ∈ [badHeaderSource, badBodySource, nonFunctionSource, unresolvedSource, returnSource, letSource],
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = true ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧
    (∀ candidate ∈ [nonLambdaSource, deepOrdinarySource, nestedSource, tupleSource, conditionalSource,
        callSource, zeroSource, multiSource, topSource],
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication candidate = false ∧
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧
    ¬ ∃ c t, ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs badHeaderSource c t := by
  have two := elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr twoEvidence
  have direct := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (.existing rfl directOld)
  have one := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (.existing rfl oneOld)
  have unifiedTwo := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr (.twoLevel rfl twoEvidence)
  have three := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr (selectedEvidence 20 21 22 [])
  have four := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr (selectedEvidence 20 21 22 [23])
  refine ⟨shallowPaths, two, direct, one, unifiedTwo, oldThreeNone, three, four,
    recognizedFailures, falseShapes, ?_⟩
  exact elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mp
    (recognizedFailures badHeaderSource (by exact .head _)).2
end Tests.ADR0323SymbolicThreeOrMoreGroupedExpectedLambdaConsumerIndependent
end
