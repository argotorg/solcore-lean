import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Eval
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
