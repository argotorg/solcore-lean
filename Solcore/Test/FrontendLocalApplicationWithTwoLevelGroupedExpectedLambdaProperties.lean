import Solcore.Frontend.LocalApplicationWithTwoLevelGroupedExpectedLambda
import Solcore.Core.Eval
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
