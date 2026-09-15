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

private def cLO := selectedAt 0 [5, 6] (lambda 10 "x") (ref 30 "ordinary")
private def cOL := selectedAt 40 [45, 46] (ref 70 "ordinary") (lambda 80 "y")
private def cLL := selectedAt 90 [95, 96] (lambda 100 "x") (lambda 120 "y")
private def coreLO := conditionalCore lambdaCore (.var 4)
private def coreOL := conditionalCore (.var 4) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore
private def expectedCore : Core.Expr := .apply (.var 0) lambdaCore
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem makeE (n : Nat) (yes no : Syntax.Expr) (yc nc : Core.Expr) (ye : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yc) (ne : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no nc) (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true) : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (selected n yes no) (conditionalCore yc nc) .word := .application boundary (applyE (n + 1)) (flagE (n + 2)) ye ne
private theorem eLO : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLO coreLO .word := makeE 0 _ _ _ _ (.expected rfl (lambdaE 10 "x")) (.ordinary rfl (ordinaryE 30)) rfl
private theorem eOL : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cOL coreOL .word := makeE 40 _ _ _ _ (.ordinary rfl (ordinaryE 70)) (.expected rfl (lambdaE 80 "y")) rfl
private theorem eLL : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs cLL coreLL .word := makeE 90 _ _ _ _ (.expected rfl (lambdaE 100 "x")) (.expected rfl (lambdaE 120 "y")) rfl
private def Provenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan innerGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨innerGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def Contract (s : Syntax.Expr) (c : Core.Expr) : Prop := isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ Provenance s c ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none
private theorem noFinite (n : Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selected n yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  cases spine with | group child => cases child with | group grandchild => cases grandchild
private theorem noConditionalSpine (n : Nat) (condition yes no : Syntax.Expr) : ∀ ns spans terminal, ¬ DirectLambdaGroupSpine (groups ns (conditional n condition yes no)) spans terminal := by
  intro ns; induction ns with
  | nil => intro _ _ spine; cases spine
  | cons head tail ih =>
      intro _ _ spine
      change DirectLambdaGroupSpine ⟨span head, .group (groups tail (conditional n condition yes no))⟩ _ _ at spine
      cases spine with | group child => exact ih _ _ child
private theorem noFiniteAt (n : Nat) (ns : List Nat) (yes no : Syntax.Expr) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false := by
  apply Bool.eq_false_iff.mpr; intro old
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp old
  exact noConditionalSpine n (ref (n + 2) "flag") yes no ns _ _ spine
private theorem conditionalOldNone (n : Nat) (ns : List Nat) (yes no : Syntax.Expr)
    (one : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (immediate : isConditionalExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (two : isTwoLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (grouped : isOneLevelGroupedExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (direct : isDirectExpectedLambdaArgumentApplication (selectedAt n ns yes no) = false)
    (inferred : elaborateRecursiveLocalComputation? inputs.names inputs.context (selectedAt n ns yes no) = none) :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (selectedAt n ns yes no) = none := by
  calc
    _ = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing one
    _ = elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing immediate finite
    _ = elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_of_existing two
    _ = elaborateLocalApplicationWithExpectedLambda? types owner inputs _ := elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing grouped
    _ = none := by
      simp only [selectedAt, atGroups, call] at direct inferred ⊢
      simpa [elaborateLocalApplicationWithExpectedLambda?, direct] using inferred
private theorem contract {s c} (e : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word) (finite : isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false) (oldNone : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s = none) : Contract s c :=
  ⟨e.classified, by cases e; rfl, by cases e; rfl, finite, e, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing (by cases e; rfl), oldNone⟩
private theorem newOldNone : ∀ source ∈ [cLO, cOL, cLL], elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = none := by
  intro source member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact conditionalOldNone 0 [5, 6] _ _ rfl rfl (noFiniteAt 0 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])
  · exact conditionalOldNone 40 [45, 46] _ _ rfl rfl (noFiniteAt 40 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])
  · exact conditionalOldNone 90 [95, 96] _ _ rfl rfl (noFiniteAt 90 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?])

/-! All three branch partitions retain the exact relation, checker, Core, type and provenance. -/
theorem all_three_two_level_grouped_conditional_partitions_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ inputs.names[3]?.map Prod.snd = some flagId ∧ Contract cLO coreLO ∧ Contract cOL coreOL ∧ Contract cLL coreLL := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact contract eLO (noFinite 0 _ _) (newOldNone cLO (by simp))
  · exact contract eOL (noFinite 40 _ _) (newOldNone cOL (by simp))
  · exact contract eLL (noFinite 90 _ _) (newOldNone cLL (by simp))

private def immediateControl := selectedAt 540 [] (lambda 550 "x") (ref 570 "ordinary")
private def oneGroupControl := selectedAt 580 [585] (lambda 590 "x") (ref 610 "ordinary")
private def lambdaControls := [lambdaApplication 620 [], lambdaApplication 650 [653],
  lambdaApplication 680 [683, 684], lambdaApplication 710 [713, 714, 715]]
private theorem immediateE :
    LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs immediateControl coreLO .word :=
  .conditional rfl (.application rfl (applyE 541) (flagE 542)
    (.expected rfl (lambdaE 550 "x")) (.ordinary rfl (ordinaryE 570)))
private theorem oneGroupE :
    LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs oneGroupControl coreLO .word :=
  .oneLevelGroupedConditional rfl (.application rfl (applyE 581) (flagE 582)
    (.expected rfl (lambdaE 590 "x")) (.ordinary rfl (ordinaryE 610)))
private theorem spineFrom {terminal : Syntax.Expr} (base : DirectLambdaGroupSpine terminal [] terminal)
    (ns : List Nat) : DirectLambdaGroupSpine (groups ns terminal) (ns.map span) terminal := by
  induction ns with | nil => exact base | cons _ _ ih => exact .group ih
private theorem spineUnique {s a b : Syntax.Expr} {xs ys : List Syntax.SourceSpan}
    (x : DirectLambdaGroupSpine s xs a) (y : DirectLambdaGroupSpine s ys b) : xs = ys ∧ a = b := by
  induction x generalizing ys b with
  | lambda => cases y; exact ⟨rfl, rfl⟩
  | group _ ih => cases y with | group z => obtain ⟨rfl, rfl⟩ := ih z; exact ⟨rfl, rfl⟩
private theorem shallowFalse (n : Nat) (ns : List Nat) (small : ns.length < 3) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (lambdaApplication n ns) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, rest, _, other⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  have lengths := congrArg List.length (spineUnique (spineFrom .lambda ns) other).1
  simp at lengths; omega
private theorem lambda0E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 620 []) expectedCore .word :=
  .existing rfl (shallowFalse 620 [] (by decide)) (.existing rfl (.existing rfl (.expected rfl (.application (applyE 621) (lambdaE 640 "x")))))
private theorem lambda1E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 650 [653]) expectedCore .word :=
  .existing rfl (shallowFalse 650 [653] (by decide)) (.existing rfl (.grouped rfl (.application (applyE 651) (lambdaE 670 "x"))))
private theorem lambda2E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 680 [683, 684]) expectedCore .word :=
  .existing rfl (shallowFalse 680 [683, 684] (by decide)) (.twoLevel rfl (.application (applyE 681) (lambdaE 700 "x")))
private theorem lambda3E : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (lambdaApplication 710 [713, 714, 715]) expectedCore .word := by
  let child : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (lambdaApplication 710 [713, 714, 715]) expectedCore .word := .application (spineFrom .lambda [713, 714, 715]) (applyE 711) (lambdaE 730 "x")
  exact .threeOrMoreGrouped rfl child.classified child
private theorem existingCheck {source core} (boundary : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source = false) (e : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs source core .word) : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = some (core, .word) := by
  rw [elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing boundary]
  exact elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) []
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def exactFuel (choice : Bool) (core : Core.Expr) : Prop := (match Core.runStateful 13 (Core.State.initial core (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 14 (Core.State.initial core (environment choice) store) = .done (.word seven) store
private def exactLambdaFuel (choice : Bool) : Prop := (match Core.runStateful 10 (Core.State.initial expectedCore (environment choice) store) with | .outOfFuel _ => True | _ => False) ∧ Core.runStateful 11 (Core.State.initial expectedCore (environment choice) store) = .done (.word seven) store
private theorem fuels : ∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core := by
  intro choice core member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cases choice <;> exact ⟨True.intro, rfl⟩

private theorem controlOptions :
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs immediateControl = some (coreLO, .word) ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs oneGroupControl = some (coreLO, .word) ∧
    (∀ source ∈ lambdaControls, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = some (expectedCore, .word)) := by
  refine ⟨existingCheck rfl immediateE, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr oneGroupE, ?_⟩
  intro source member; simp only [lambdaControls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> first | exact existingCheck rfl lambda0E | exact existingCheck rfl lambda1E | exact existingCheck rfl lambda2E | exact existingCheck rfl lambda3E

/-! New and predecessor controls retain their exact fuel cutoffs and literal store. -/
theorem both_choices_have_exact_fuel_and_preserve_store :
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL] → exactFuel choice core) ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs immediateControl = some (coreLO, .word) ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs oneGroupControl = some (coreLO, .word) ∧
    (∀ source ∈ lambdaControls, elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = some (expectedCore, .word)) ∧
    (∀ choice, exactFuel choice coreLO ∧ exactLambdaFuel choice) := by
  refine ⟨fuels, controlOptions.1, controlOptions.2.1, controlOptions.2.2, ?_⟩
  intro choice; exact ⟨fuels choice coreLO (by simp), by cases choice <;> exact ⟨True.intro, rfl⟩⟩

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

private theorem failuresStayFinal : ∀ source ∈ failures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source) = none := by
  intro source member
  have h := failuresFinal source member
  exact ⟨h.1, h.2, by simp [h.1, h.2]⟩

private def threeGroupConditional := selectedAt 760 [765, 766, 767] (lambda 770 "x") (ref 790 "ordinary")
private def allOrdinarySource := selectedAt 800 [805, 806] (ref 810 "ordinary") (ref 820 "ordinary")
private def allOrdinaryCore := conditionalCore (.var 4) (.var 4)
private def groupedOnlySource := selectedAt 830 [835, 836] (groups [840] (lambda 850 "x")) (ref 870 "ordinary")
private def nestedOnlySource := selectedAt 880 [885, 886] (nestedLambdaCall 890) (ref 910 "ordinary")
private def zeroArgument : Syntax.Expr := ⟨span 920, .call (ref 921 "apply") ⟨span 922, []⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 930, .call (ref 931 "apply") ⟨span 932, [lambda 940 "x", ref 960 "ordinary"]⟩⟩
private def topLevelNonCall := groups [970, 971] (conditional 972 (ref 974 "flag") (lambda 980 "x") (ref 1000 "ordinary"))
private theorem allOrdinaryE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs allOrdinarySource allOrdinaryCore .word :=
  .existing rfl (noFinite 800 _ _) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 801) (.group (.group (.conditional (flagE 802) (ordinaryE 810) (ordinaryE 820))))))))
private theorem ordinaryFalse (n : Nat) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (ordinaryApplication n) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp h
  cases spine
private theorem ordinaryApplicationE : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (ordinaryApplication 1010) ordinaryCore .word :=
  .existing rfl (ordinaryFalse 1010) (.existing rfl (.existing rfl (.ordinary rfl (.application (applyE 1011) (ordinaryE 1030)))))
private def completeNeighbors : List (Syntax.Expr × Option (Core.Expr × Core.Ty)) :=
  [(oneGroupControl, some (coreLO, .word)), (threeGroupConditional, none),
   (allOrdinarySource, some (allOrdinaryCore, .word)), (groupedOnlySource, none),
   (nestedOnlySource, none), (immediateControl, some (coreLO, .word)),
   (lambdaApplication 620 [], some (expectedCore, .word)),
   (lambdaApplication 650 [653], some (expectedCore, .word)),
   (lambdaApplication 680 [683, 684], some (expectedCore, .word)),
   (lambdaApplication 710 [713, 714, 715], some (expectedCore, .word)),
   (ordinaryApplication 1010, some (ordinaryCore, .word)), (zeroArgument, none),
   (multipleArguments, none), (topLevelNonCall, none)]
private def CompleteOption (item : Syntax.Expr × Option (Core.Expr × Core.Ty)) : Prop :=
  isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧
  elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧
  elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧
  (if isOneLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 then
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1
   else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs item.1)
private theorem dispatchRoute (source : Syntax.Expr) :
    (if isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source then
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source
     else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs source) := by
  cases h : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication source
  · exact elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing h
  · exact elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional h
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := ⟨boundary, rejected, exact, dispatchRoute source⟩
private theorem completeOptionsExact : ∀ item ∈ completeNeighbors, CompleteOption item := by
  intro item member; simp only [completeNeighbors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact completeOption (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr oneGroupE)
  · exact completeOption (by simpa only [threeGroupConditional] using conditionalOldNone 760 [765, 766, 767] (lambda 770 "x") (ref 790 "ordinary") rfl rfl (noFiniteAt 760 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (existingCheck rfl allOrdinaryE)
  · exact completeOption (by simpa only [groupedOnlySource] using conditionalOldNone 830 [835, 836] (groups [840] (lambda 850 "x")) (ref 870 "ordinary") rfl rfl (noFiniteAt 830 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (by simpa only [nestedOnlySource] using conditionalOldNone 880 [885, 886] (nestedLambdaCall 890) (ref 910 "ordinary") rfl rfl (noFiniteAt 880 _ _ _) rfl rfl rfl (by simp [selectedAt, atGroups, groups, conditional, call, nestedLambdaCall, lambda, body, ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?]))
  · exact completeOption (existingCheck rfl immediateE)
  · exact completeOption (existingCheck rfl lambda0E)
  · exact completeOption (existingCheck rfl lambda1E)
  · exact completeOption (existingCheck rfl lambda2E)
  · exact completeOption (existingCheck rfl lambda3E)
  · exact completeOption (existingCheck rfl ordinaryApplicationE)
  · exact completeOption rfl
  · exact completeOption rfl
  · exact completeOption rfl

/-! Selected failures remain final; every false shape retains the complete ADR-0327 Option. -/
theorem recognized_failures_and_complete_adr0327_options_are_exact :
    (∀ source ∈ failures, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication source then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs source) = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ t o i s, isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → (if isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨failuresStayFinal, completeOptionsExact, by intro _ _ _ _ h; simp [h]⟩

end Tests.ADR0328TwoLevelGroupedConditionalSymbolicConsumerIndependent
