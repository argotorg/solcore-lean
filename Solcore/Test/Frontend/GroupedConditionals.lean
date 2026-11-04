import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Core.Eval
import Solcore.Frontend.GroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.OneLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Core.Machine
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.ThreeLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.TwoLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication

/-!
# Grouped conditional tests

Expected lambda arguments under grouped conditionals: conditional, one- to three-level groups and the
generic adapter.
-/

section
-- leanmerge: from Solcore.Test.FrontendConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for conditional expected-lambda arguments. -/
set_option autoImplicit false
namespace Tests.ADR0324ConditionalExpectedLambdaArgumentApplicationConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ConditionalExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 324
private def foreignOwner := declaration 9324
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def applyId := localId owner 17
private def opaqueId := localId foreignOwner 700
private def duplicateId := localId owner 3
private def flagId := localId foreignOwner 701
private def ordinaryId := localId owner 29
private def wrongId := localId foreignOwner 702
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell (.function .word .unit)⟩, ⟨"apply", duplicateId, .unit⟩, ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩, ⟨"wrong", wrongId, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "conditional-expected-lambda.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block := ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩ none (body n name)⟩
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr := ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr := ⟨span (n + 3), .conditional condition (span (n + 4)) yes (span (n + 5)) no⟩
private def source (n : Nat) (callee condition yes no : Syntax.Expr) : Syntax.Expr := call n callee (conditional n condition yes no)
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref n "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide)
    (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide)
    (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem wrongElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref n "wrong") (.var 5) .word :=
  .pure (.identifier (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "opaque" ≠ "wrong"; decide)
    (.tail (by change "apply" ≠ "wrong"; decide) (.tail (by change "flag" ≠ "wrong"; decide) (.tail (by change "ordinary" ≠ "wrong"; decide) .head))))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
private theorem missingRejected (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "missing") = none := by
  have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
  simp only [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
    resolveLocalExpression?, absent, Option.map_none, bind, Option.bind_none]
private theorem lambdaElaboration (n : Nat) (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs
      (lambda n name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem applyChecked (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") = some (.var 0, .function functionType .word) := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration n)
private theorem flagChecked (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "flag") = some (.var 3, .bool) := elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration n)
private theorem wrongChecked (n : Nat) : elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") = some (.var 5, .word) := elaborateRecursiveLocalComputation?_iff.mpr (wrongElaboration n)
private def lambdaOrdinarySource := source 0 (ref 1 "apply") (ref 2 "flag") (lambda 10 "x") (ref 30 "ordinary")
private def ordinaryLambdaSource := source 40 (ref 41 "apply") (ref 42 "flag") (ref 43 "ordinary") (lambda 50 "x")
private def lambdaLambdaSource := source 60 (ref 61 "apply") (ref 62 "flag") (lambda 70 "x") (lambda 80 "y")
private def lambdaOrdinaryCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
private def ordinaryLambdaCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) (.var 4) lambdaCore)
private def lambdaLambdaCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) lambdaCore lambdaCore)
private theorem exactContract (n : Nat) {callee condition yes no : Syntax.Expr} {functionCore conditionCore yesCore noCore : Core.Expr}
    (boundary : (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true)
    (calleeEvidence : RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function functionType .word))
    (conditionEvidence : RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool)
    (yesEvidence : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yesCore)
    (noEvidence : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no noCore) :
    isConditionalExpectedLambdaArgumentApplication (source n callee condition yes no) = true ∧
    ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source n callee condition yes no)
      (.apply functionCore (.ifE conditionCore yesCore noCore)) .word ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs (source n callee condition yes no) = some (.apply functionCore (.ifE conditionCore yesCore noCore), .word) ∧
    Core.HasType inputs.context.values (.apply functionCore (.ifE conditionCore yesCore noCore)) .word ∧
    ∃ callSpan argumentsSpan conditionalSpan question colon retainedCallee retainedCondition retainedYes retainedNo
        retainedFunction retainedConditionCore retainedYesCore retainedNoCore,
      source n callee condition yes no = ⟨callSpan, .call retainedCallee ⟨argumentsSpan, [⟨conditionalSpan, .conditional retainedCondition question retainedYes colon retainedNo⟩]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context retainedCallee retainedFunction (.function functionType .word) ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context retainedCondition retainedConditionCore .bool ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs functionType retainedYes retainedYesCore ∧
      ConditionalExpectedLambdaBranchElaborates types owner inputs functionType retainedNo retainedNoCore ∧
      Core.Expr.apply functionCore (.ifE conditionCore yesCore noCore) = Core.Expr.apply retainedFunction (.ifE retainedConditionCore retainedYesCore retainedNoCore) := by
  let evidence : ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source n callee condition yes no) (.apply functionCore (.ifE conditionCore yesCore noCore)) .word :=
    .application boundary calleeEvidence conditionEvidence yesEvidence noEvidence
  exact ⟨evidence.classified, evidence, elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr evidence,
    evidence.core_hasType, ⟨span n, span (n + 1), span (n + 3), span (n + 4), span (n + 5), callee,
      condition, yes, no, functionCore, conditionCore, yesCore, noCore, rfl, calleeEvidence, conditionEvidence, yesEvidence, noEvidence, rfl⟩⟩
private theorem allThreeBranchPartitionsProof :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    ∀ item ∈ [(lambdaOrdinarySource, lambdaOrdinaryCore), (ordinaryLambdaSource, ordinaryLambdaCore), (lambdaLambdaSource, lambdaLambdaCore)],
      isConditionalExpectedLambdaArgumentApplication item.1 = true ∧
      ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧
      elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = some (item.2, .word) ∧
      Core.HasType inputs.context.values item.2 .word ∧
      ∃ callSpan argumentsSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore,
        item.1 = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨conditionalSpan, .conditional condition question yes colon no⟩]⟩⟩ ∧
        RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function functionType .word) ∧
        RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧
        ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yesCore ∧
        ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no noCore ∧
        item.2 = .apply functionCore (.ifE conditionCore yesCore noCore) := by
  refine ⟨rfl, rfl, ?_⟩
  intro item membership; simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact exactContract 0 rfl (applyElaboration 1) (flagElaboration 2) (.expected rfl (lambdaElaboration 10 "x")) (.ordinary rfl (ordinaryElaboration 30))
  · exact exactContract 40 rfl (applyElaboration 41) (flagElaboration 42) (.ordinary rfl (ordinaryElaboration 43)) (.expected rfl (lambdaElaboration 50 "x"))
  · exact exactContract 60 rfl (applyElaboration 61) (flagElaboration 62) (.expected rfl (lambdaElaboration 70 "x")) (.expected rfl (lambdaElaboration 80 "y"))
/-- All three immediate branch partitions retain literal parameter and source evidence. -/
theorem all_three_branch_partitions_have_exact_semantics : inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧ ∀ item ∈ [(lambdaOrdinarySource, lambdaOrdinaryCore), (ordinaryLambdaSource, ordinaryLambdaCore), (lambdaLambdaSource, lambdaLambdaCore)], isConditionalExpectedLambdaArgumentApplication item.1 = true ∧ ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 item.2 .word ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = some (item.2, .word) ∧ Core.HasType inputs.context.values item.2 .word ∧ ∃ callSpan argumentsSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore, item.1 = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨conditionalSpan, .conditional condition question yes colon no⟩]⟩⟩ ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function functionType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs functionType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs functionType no noCore ∧ item.2 = .apply functionCore (.ifE conditionCore yesCore noCore) := allThreeBranchPartitionsProof
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private theorem finish {choice : Bool} {argument : Core.Expr} {captured : Core.Environment}
    (argumentRuns : Core.Evaluates (environment choice) store argument (.closure .word .word (.var 0) captured) store) :
    Core.Evaluates (environment choice) store (.apply (.var 0) argument) (.word seven) store :=
  .apply (.var rfl) argumentRuns (.apply (.var rfl) .word (.var rfl))
private theorem lambdaOrdinaryRuns (choice : Bool) : Core.Evaluates (environment choice) store lambdaOrdinaryCore (.word seven) store := by
  cases choice <;> first | exact finish (.ifFalse (.var rfl) (.var rfl)) | exact finish (.ifTrue (.var rfl) .lambda)
private theorem ordinaryLambdaRuns (choice : Bool) : Core.Evaluates (environment choice) store ordinaryLambdaCore (.word seven) store := by
  cases choice <;> first | exact finish (.ifFalse (.var rfl) .lambda) | exact finish (.ifTrue (.var rfl) (.var rfl))
private theorem lambdaLambdaRuns (choice : Bool) : Core.Evaluates (environment choice) store lambdaLambdaCore (.word seven) store := by
  cases choice <;> exact finish (by first | exact .ifFalse (.var rfl) .lambda | exact .ifTrue (.var rfl) .lambda)
private theorem bothChoicesProof :
    (∀ choice, Core.Evaluates (environment choice) store lambdaOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store ordinaryLambdaCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store lambdaLambdaCore (.word seven) store) := ⟨lambdaOrdinaryRuns, ordinaryLambdaRuns, lambdaLambdaRuns⟩
/-- Both runtime choices execute all three literal Core modes without store change. -/
theorem both_choices_execute_all_three_cores_without_store_change : (∀ choice, Core.Evaluates (environment choice) store lambdaOrdinaryCore (.word seven) store) ∧ (∀ choice, Core.Evaluates (environment choice) store ordinaryLambdaCore (.word seven) store) ∧ (∀ choice, Core.Evaluates (environment choice) store lambdaLambdaCore (.word seven) store) := bothChoicesProof
private def badHeader (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), "x"⟩⟩, ⟨span (n + 2), .inferred ⟨span (n + 2), "y"⟩⟩]⟩ none (body n "x")⟩
private def badBody (n : Nat) : Syntax.Expr := ⟨span n, .lambda (span (n + 1)) ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), "x"⟩⟩]⟩ none ⟨span (n + 3), [⟨span (n + 4), .returnStmt none⟩]⟩⟩
private theorem badHeaderBranchRejected (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badHeader n) functionType = none := by
  have rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner inputs (badHeader n) functionType = none := by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeader; rfl
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (badHeader n) = true by rfl]; exact rejected
private theorem badBodyBranchRejected (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (badBody n) functionType = none := by
  have rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      types owner inputs (badBody n) functionType = none := by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBody functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (badBody n) = true by rfl]; exact rejected
private theorem wrongBranchRejected (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (ref n "wrong") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (ref n "wrong") = false by rfl]; simp [wrongChecked, functionType]
private theorem missingBranchRejected (n : Nat) : elaborateConditionalExpectedLambdaBranch? types owner inputs (ref n "missing") functionType = none := by
  unfold elaborateConditionalExpectedLambdaBranch?; rw [show isImmediateExpectedComputationLambda (ref n "missing") = false by rfl]; simp [missingRejected]
private def representativeFailure := source 160 (ref 161 "apply") (ref 162 "flag") (badHeader 170) (ref 180 "ordinary")
private def failureSources : List Syntax.Expr := [
  source 100 (ref 101 "apply") (ref 102 "wrong") (lambda 110 "x") (ref 120 "ordinary"),
  source 130 (ref 131 "apply") (ref 132 "missing") (lambda 140 "x") (ref 150 "ordinary"),
  representativeFailure,
  source 190 (ref 191 "apply") (ref 192 "flag") (ref 193 "ordinary") (badHeader 200),
  source 210 (ref 211 "apply") (ref 212 "flag") (badBody 220) (ref 230 "ordinary"),
  source 240 (ref 241 "apply") (ref 242 "flag") (lambda 250 "x") (ref 260 "wrong"),
  source 270 (ref 271 "apply") (ref 272 "flag") (lambda 280 "x") (ref 290 "missing"),
  source 300 (ref 301 "flag") (ref 302 "flag") (lambda 310 "x") (ref 320 "ordinary"),
  source 330 (ref 331 "missing") (ref 332 "flag") (lambda 340 "x") (ref 350 "ordinary")]
private theorem recognizedFailures : ∀ candidate ∈ failureSources,
    isConditionalExpectedLambdaArgumentApplication candidate = true ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  intro candidate membership
  simp only [failureSources, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨rfl, elaborateConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr ?_⟩ <;>
    rintro ⟨_, _, evidence⟩ <;> cases evidence with
    | application _ calleeEvidence conditionEvidence yesEvidence noEvidence =>
      first
      | have h := elaborateRecursiveLocalComputation?_iff.mpr calleeEvidence; rw [flagChecked] at h; cases h
      | have h := elaborateRecursiveLocalComputation?_iff.mpr calleeEvidence; rw [missingRejected] at h; cases h
      | have callee := elaborateRecursiveLocalComputation?_iff.mpr calleeEvidence
        rw [applyChecked] at callee; cases callee
        first
        | have h := elaborateRecursiveLocalComputation?_iff.mpr conditionEvidence; rw [wrongChecked] at h; cases h
        | have h := elaborateRecursiveLocalComputation?_iff.mpr conditionEvidence; rw [missingRejected] at h; cases h
        | have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr yesEvidence; rw [badHeaderBranchRejected] at h; cases h
        | have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr noEvidence; rw [badHeaderBranchRejected] at h; cases h
        | have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr yesEvidence; rw [badBodyBranchRejected] at h; cases h
        | have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr noEvidence; rw [wrongBranchRejected] at h; cases h
        | have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr noEvidence; rw [missingBranchRejected] at h; cases h
private def groups (positions : List Nat) (inner : Syntax.Expr) : Syntax.Expr :=
  positions.foldr (fun n child => ⟨span n, .group child⟩) inner
private def oldSource (positions : List Nat) : Syntax.Expr := call 400 (ref 401 "apply") (groups positions (lambda 410 "x"))
private def oldCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem groupSpine (positions : List Nat) : DirectLambdaGroupSpine
    (groups positions (lambda 410 "x")) (positions.map span) (lambda 410 "x") := by
  induction positions with | nil => exact .lambda | cons head tail ih => exact .group ih
private theorem directOld : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs (oldSource []) oldCore .word :=
  .existing rfl (.existing rfl (.expected rfl (.application (applyElaboration 401) (lambdaElaboration 410 "x"))))
private theorem oneOld : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs (oldSource [420]) oldCore .word :=
  .existing rfl (.grouped rfl (.application (applyElaboration 401) (lambdaElaboration 410 "x")))
private theorem twoOld : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs (oldSource [420, 421]) oldCore .word :=
  .twoLevel rfl (.application (applyElaboration 401) (lambdaElaboration 410 "x"))
private theorem deepOld (first second third : Nat) (rest : List Nat) :
    ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
      (oldSource (first :: second :: third :: rest)) oldCore .word :=
  .application (groupSpine _) (applyElaboration 401) (lambdaElaboration 410 "x")
private def allOrdinary := source 500 (ref 501 "apply") (ref 502 "flag") (ref 503 "ordinary") (ref 504 "ordinary")
private def allOrdinaryCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4))
private theorem allOrdinaryOld : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs allOrdinary allOrdinaryCore .word :=
  .existing rfl (.existing rfl (.ordinary rfl (.application (applyElaboration 501)
    (.conditional (flagElaboration 502) (ordinaryElaboration 503) (ordinaryElaboration 504)))))
private def groupedBranch := source 510 (ref 511 "apply") (ref 512 "flag")
  (groups [513] (lambda 520 "x")) (ref 530 "ordinary")
private def nestedBranch := call 540 (ref 541 "ordinary") (lambda 550 "x")
private def nestedConditional := source 560 (ref 561 "apply") (ref 562 "flag") nestedBranch (ref 570 "ordinary")
private def mixedGrouped := source 580 (ref 581 "apply") (ref 582 "flag") (lambda 590 "x") (groups [600] (lambda 610 "y"))
private def mixedNested := source 620 (ref 621 "apply") (ref 622 "flag") (lambda 630 "x") nestedBranch
private theorem nestedRecursiveRejected : elaborateRecursiveLocalComputation?
    inputs.names inputs.context nestedBranch = none := by
  simp [nestedBranch, call, lambda, body, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]
private theorem groupedRecursiveRejected : elaborateRecursiveLocalComputation? inputs.names inputs.context
    (groups [600] (lambda 610 "y")) = none := by
  simp [groups, lambda, body, ref, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?]
private theorem mixedOrdinaryFailure (n calleeAt conditionAt lambdaAt : Nat) {candidate : Syntax.Expr}
    (ordinary : isImmediateExpectedComputationLambda candidate = false)
    (rejected : elaborateRecursiveLocalComputation? inputs.names inputs.context candidate = none) :
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs
      (source n (ref calleeAt "apply") (ref conditionAt "flag") (lambda lambdaAt "x") candidate) = none := by
  apply elaborateConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mpr
  rintro ⟨_, _, evidence⟩
  cases evidence with | application _ calleeEvidence _ _ noEvidence =>
    have callee := elaborateRecursiveLocalComputation?_iff.mpr calleeEvidence
    rw [applyChecked] at callee
    cases callee
    have h := elaborateConditionalExpectedLambdaBranch?_iff.mpr noEvidence
    have branchNone : elaborateConditionalExpectedLambdaBranch?
        types owner inputs candidate functionType = none := by
      unfold elaborateConditionalExpectedLambdaBranch?; rw [ordinary]; simp [rejected]
    rw [branchNone] at h
    cases h
private theorem mixedGroupedRejected : elaborateConditionalExpectedLambdaArgumentApplication?
    types owner inputs mixedGrouped = none := mixedOrdinaryFailure 580 581 582 590 rfl groupedRecursiveRejected
private theorem mixedNestedRejected : elaborateConditionalExpectedLambdaArgumentApplication?
    types owner inputs mixedNested = none := mixedOrdinaryFailure 620 621 622 630 rfl nestedRecursiveRejected
private def groupedWhole := call 640 (ref 641 "apply") (groups [642]
  (conditional 643 (ref 644 "flag") (lambda 650 "x") (ref 660 "ordinary")))
private def tupleCall := call 670 (ref 671 "apply") ⟨span 672, .tuple ⟨span 673, [lambda 680 "x", ref 690 "ordinary"]⟩⟩
private def callCall := call 700 (ref 701 "apply") (call 702 (ref 703 "ordinary") (lambda 710 "x"))
private def zeroCall : Syntax.Expr := ⟨span 720, .call (ref 721 "apply") ⟨span 722, []⟩⟩
private def multiCall : Syntax.Expr := ⟨span 730, .call (ref 731 "apply")
  ⟨span 732, [conditional 733 (ref 734 "flag") (lambda 740 "x") (ref 750 "ordinary"), ref 751 "ordinary"]⟩⟩
private def falseSources := [allOrdinary, oldSource [], oldSource [420], oldSource [420, 421],
  groupedBranch, groupedWhole, nestedConditional, tupleCall, callCall, zeroCall, multiCall,
  conditional 760 (ref 761 "flag") (lambda 770 "x") (ref 780 "ordinary")]
private theorem falseShapes : ∀ candidate ∈ falseSources,
    isConditionalExpectedLambdaArgumentApplication candidate = false ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none := by
  intro candidate membership
  simp only [falseSources, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem failuresAndBoundariesProof :
    (∀ candidate ∈ failureSources, isConditionalExpectedLambdaArgumentApplication candidate = true ∧
      elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧
    (∀ candidate ∈ falseSources, isConditionalExpectedLambdaArgumentApplication candidate = false ∧
      elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs allOrdinary = some (allOrdinaryCore, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource []) = some (oldCore, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource [420]) = some (oldCore, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource [420, 421]) = some (oldCore, .word) ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (oldSource [420, 421, 422]) = some (oldCore, .word) ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (oldSource [420, 421, 422, 423, 424, 425]) = some (oldCore, .word) ∧
    isConditionalExpectedLambdaArgumentApplication mixedGrouped = true ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs mixedGrouped = none ∧
    isConditionalExpectedLambdaArgumentApplication mixedNested = true ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs mixedNested = none ∧
    ¬ ∃ core type, ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs representativeFailure core type := by
  have allOrdinaryChecked := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr allOrdinaryOld
  have directChecked := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr directOld
  have oneChecked := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr oneOld
  have twoChecked := elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?_iff.mpr twoOld
  have threeChecked := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr (deepOld 420 421 422 [])
  have deeperChecked := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr (deepOld 420 421 422 [423, 424, 425])
  refine ⟨recognizedFailures, falseShapes, allOrdinaryChecked, directChecked, oneChecked, twoChecked,
    threeChecked, deeperChecked, rfl, mixedGroupedRejected, rfl, mixedNestedRejected, ?_⟩
  exact elaborateConditionalExpectedLambdaArgumentApplication?_eq_none_iff.mp
    (recognizedFailures representativeFailure (by simp [failureSources])).2
/-- Recognized failures are final while all frozen source boundaries remain exact. -/
theorem recognized_failures_and_old_boundaries_are_exact : (∀ candidate ∈ failureSources, isConditionalExpectedLambdaArgumentApplication candidate = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧ (∀ candidate ∈ falseSources, isConditionalExpectedLambdaArgumentApplication candidate = false ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs candidate = none) ∧ elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs allOrdinary = some (allOrdinaryCore, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource []) = some (oldCore, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource [420]) = some (oldCore, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (oldSource [420, 421]) = some (oldCore, .word) ∧ elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (oldSource [420, 421, 422]) = some (oldCore, .word) ∧ elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs (oldSource [420, 421, 422, 423, 424, 425]) = some (oldCore, .word) ∧ isConditionalExpectedLambdaArgumentApplication mixedGrouped = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs mixedGrouped = none ∧ isConditionalExpectedLambdaArgumentApplication mixedNested = true ∧ elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs mixedNested = none ∧ ¬ ∃ core type, ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs representativeFailure core type := failuresAndBoundariesProof
end Tests.ADR0324ConditionalExpectedLambdaArgumentApplicationConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendGenericGroupedConditionalProperties
/-!
Compact independent symbolic coverage for the generic grouped-conditional
adapter and its generic-first local-application wrapper.
-/

set_option autoImplicit false

namespace Tests.FrontendGenericGroupedConditionalProperties

open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"GenericGroupedConditional", by decide⟩], by decide⟩⟩, n⟩

private def owner := declaration 340
private def localId (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def applyId := localId 0
private def flagId := localId 1
private def ordinaryId := localId 2
private def wrongId := localId 3
private def functionType : Core.Ty := .function .word .word
private def types : TypeNameTable := []
private def inputs : LocalTypeInputs := ⟨
  [⟨"apply", applyId, .function functionType .word⟩,
   ⟨"flag", flagId, .bool⟩,
   ⟨"ordinary", ordinaryId, functionType⟩,
   ⟨"wrong", wrongId, .word⟩],
  by decide⟩

private def file : Syntax.SourceId := ⟨.main, "generic-grouped-conditional.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span n, name⟩⟩
private def groups (ns : List Nat) (expression : Syntax.Expr) : Syntax.Expr :=
  ns.foldr (fun n inner => ⟨span n, .group inner⟩) expression
private def groupIndices (n depth : Nat) : List Nat :=
  (List.range depth).map (n + 5 + ·)
private def call (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def body (n : Nat) (name : String) : Syntax.Block :=
  ⟨span (n + 3), [⟨span (n + 4), .returnStmt (some (ref (n + 5) name))⟩]⟩
private def lambda (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .lambda (span (n + 1))
    ⟨span (n + 2), [⟨span (n + 2), .inferred ⟨span (n + 2), name⟩⟩]⟩
    none (body n name)⟩
private def conditional (n : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr :=
  ⟨span (n + 2), .conditional condition (span (n + 3)) yes (span (n + 4)) no⟩
private def selected (n depth : Nat) (condition yes no : Syntax.Expr) : Syntax.Expr :=
  call n (ref (n + 1) "apply")
    (groups (groupIndices n depth) (conditional n condition yes no))

private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def conditionalCore (yes no : Core.Expr) : Core.Expr :=
  .apply (.var 0) (.ifE (.var 1) yes no)

private theorem applyE (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem flagE (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "flag") (.var 1) .bool :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "flag"; decide) .head))
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) .head))

private theorem ordinaryE (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "ordinary") (.var 2) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem wrongE (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "wrong") (.var 3) .word :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "wrong"; decide)
      (.tail (by change "flag" ≠ "wrong"; decide)
        (.tail (by change "ordinary" ≠ "wrong"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

private theorem applyC (n : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "apply") =
      some (.var 0, .function functionType .word) :=
  elaborateRecursiveLocalComputation?_iff.mpr (applyE n)

private theorem wrongC (n : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (ref n "wrong") =
      some (.var 3, .word) :=
  elaborateRecursiveLocalComputation?_iff.mpr (wrongE n)

private theorem lambdaE (n : Nat) (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambda n name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word, body n name, .word, .word⟩) <;>
    first
    | exact ExpectedUnaryLambdaHeaderDeclares.lambda
        ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
    | exact .word
    | exact ComputationReturnTreeElaborates.expression
        (.pure (.identifier .head) (.var .head) (.var .head))

private theorem groupsSpine {terminal : Syntax.Expr}
    (base : ConditionalGroupSpine terminal [] terminal) (ns : List Nat) :
    ConditionalGroupSpine (groups ns terminal) (ns.map span) terminal := by
  induction ns with
  | nil => exact base
  | cons head tail ih => exact .group ih

private theorem spineUnique {source leftTerminal rightTerminal : Syntax.Expr}
    {leftSpans rightSpans : List Syntax.SourceSpan}
    (left : ConditionalGroupSpine source leftSpans leftTerminal)
    (right : ConditionalGroupSpine source rightSpans rightTerminal) :
    leftSpans = rightSpans ∧ leftTerminal = rightTerminal := by
  have leftChecked := peelConditionalGroupSpine?_iff.mpr left
  have rightChecked := peelConditionalGroupSpine?_iff.mpr right
  rw [leftChecked] at rightChecked
  simpa using rightChecked

private theorem makeE (n depth : Nat) (minimum : 8 ≤ depth)
    (yes no : Syntax.Expr) (yesCore noCore : Core.Expr)
    (yesE : ConditionalExpectedLambdaBranchElaborates
      types owner inputs functionType yes yesCore)
    (noE : ConditionalExpectedLambdaBranchElaborates
      types owner inputs functionType no noCore)
    (boundary : (isImmediateExpectedComputationLambda yes ||
      isImmediateExpectedComputationLambda no) = true) :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs
      (selected n depth (ref (n + 2) "flag") yes no)
      (conditionalCore yesCore noCore) .word := by
  apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
    (groupsSpine ConditionalGroupSpine.conditional (groupIndices n depth))
  · simpa [groupIndices] using minimum
  · exact boundary
  · exact applyE (n + 1)
  · exact flagE (n + 2)
  · exact yesE
  · exact noE

private theorem selectedClassified (n depth : Nat) (minimum : 8 ≤ depth)
    (condition yes no : Syntax.Expr)
    (boundary : (isImmediateExpectedComputationLambda yes ||
      isImmediateExpectedComputationLambda no) = true) :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication
      (selected n depth condition yes no) = true := by
  unfold selected
  apply isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication_iff.mpr
  refine ⟨(groupIndices n depth).map span, span (n + 2), span (n + 3), span (n + 4),
    condition, yes, no, ?_, ?_, boundary⟩
  · exact groupsSpine ConditionalGroupSpine.conditional (groupIndices n depth)
  · simpa [groupIndices] using minimum

private def source8 := selected 0 8 (ref 2 "flag") (lambda 40 "x") (ref 70 "ordinary")
private def source9 := selected 100 9 (ref 102 "flag") (ref 170 "ordinary") (lambda 140 "y")
private def source16 := selected 200 16 (ref 202 "flag") (lambda 240 "x") (lambda 270 "y")
private def coreLO := conditionalCore lambdaCore (.var 2)
private def coreOL := conditionalCore (.var 2) lambdaCore
private def coreLL := conditionalCore lambdaCore lambdaCore

private theorem e8 :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source8 coreLO .word :=
  makeE 0 8 (by decide) _ _ _ _
    (.expected rfl (lambdaE 40 "x")) (.ordinary rfl (ordinaryE 70)) rfl
private theorem e9 :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source9 coreOL .word :=
  makeE 100 9 (by decide) _ _ _ _
    (.ordinary rfl (ordinaryE 170)) (.expected rfl (lambdaE 140 "y")) rfl
private theorem e16 :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source16 coreLL .word :=
  makeE 200 16 (by decide) _ _ _ _
    (.expected rfl (lambdaE 240 "x")) (.expected rfl (lambdaE 270 "y")) rfl

private def SuccessContract (source : Syntax.Expr) (core : Core.Expr) : Prop :=
  isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
  EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs source core .word ∧
  elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
    types owner inputs source = some (core, .word) ∧
  LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
    types owner inputs source core .word ∧
  elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
    types owner inputs source = some (core, .word) ∧
  Core.HasType inputs.context.values core .word ∧
  ((isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = true ∧
      EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core .word) ∨
    (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source = false ∧
      LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
        types owner inputs source core .word))

private theorem successContract {source core}
    (child : EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core .word) : SuccessContract source core := by
  let wrapped : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs source core .word :=
    .eightOrMoreGroupedConditional child.classified child
  exact ⟨child.classified, child,
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    wrapped,
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mpr wrapped,
    wrapped.core_hasType, wrapped.provenance⟩

/-- Depths eight, nine and a deeper finite spine use one generic relation and
retain executable/declarative correspondence, typing and wrapper provenance. -/
theorem depths_eight_nine_and_sixteen_have_generic_semantics :
    SuccessContract source8 coreLO ∧
    SuccessContract source9 coreOL ∧
    SuccessContract source16 coreLL :=
  ⟨successContract e8, successContract e9, successContract e16⟩

/-- The generic classifier is disjoint from every frozen depth zero through seven. -/
theorem depths_below_eight_are_not_generic (n depth : Nat) (small : depth < 8)
    (yes no : Syntax.Expr) :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication
      (selected n depth (ref (n + 2) "flag") yes no) = false := by
  apply Bool.eq_false_iff.mpr
  intro classified
  obtain ⟨spans, _, _, _, _, _, _, spine, minimum, _⟩ :=
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication_iff.mp classified
  have known := groupsSpine (ConditionalGroupSpine.conditional
    (span := span (n + 2)) (question := span (n + 3)) (colon := span (n + 4))
    (condition := ref (n + 2) "flag") (yes := yes) (no := no)) (groupIndices n depth)
  have same := spineUnique known spine
  have lengths := congrArg List.length same.1
  simp [groupIndices] at lengths
  omega

private def failed :=
  selected 400 8 (ref 402 "wrong") (lambda 440 "x") (ref 470 "ordinary")

/-- Once the generic source partition is selected, a bad condition is final and
the wrapper does not retry the frozen predecessor. -/
theorem selected_failure_is_final :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication failed = true ∧
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs failed = none ∧
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs failed =
        elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
          types owner inputs failed ∧
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs failed = none := by
  have boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication failed = true := by
    exact selectedClassified 400 8 (by decide) (ref 402 "wrong")
      (lambda 440 "x") (ref 470 "ordinary") rfl
  have rejected :
      elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
        types owner inputs failed = none := by
    have spine := groupsSpine (ConditionalGroupSpine.conditional
      (span := span 402) (question := span 403) (colon := span 404)
      (condition := ref 402 "wrong") (yes := lambda 440 "x")
      (no := ref 470 "ordinary")) (groupIndices 400 8)
    unfold failed selected
    simp only [call,
      elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?]
    unfold conditional at spine ⊢
    rw [peelConditionalGroupSpine?_iff.mpr spine]
    simp [groupIndices, applyC, wrongC]
  have route :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
      (types := types) (owner := owner) (inputs := inputs) boundary
  exact ⟨boundary, rejected, route, route.trans rejected⟩

private def source7 := call 500 (ref 501 "apply")
  (groups [505, 506, 507, 508, 509, 510, 511]
    (conditional 500 (ref 502 "flag") (lambda 540 "x") (ref 570 "ordinary")))

private theorem sevenE :
    SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs source7 coreLO .word := by
  exact SevenLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
    rfl (applyE 501) (flagE 502)
    (.expected rfl (lambdaE 540 "x")) (.ordinary rfl (ordinaryE 570))

private theorem source7NotGeneric :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source7 = false := by
  apply Bool.eq_false_iff.mpr
  intro classified
  obtain ⟨spans, _, _, _, _, _, _, spine, minimum, _⟩ :=
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication_iff.mp classified
  have known := groupsSpine (ConditionalGroupSpine.conditional
    (span := span 502) (question := span 503) (colon := span 504)
    (condition := ref 502 "flag") (yes := lambda 540 "x")
    (no := ref 570 "ordinary")) [505, 506, 507, 508, 509, 510, 511]
  have lengths := congrArg List.length (spineUnique known spine).1
  simp at lengths
  omega

/-- On the false side the wrapper preserves the complete predecessor `Option`,
including its proof object and Core type. -/
theorem false_side_preserves_complete_seven_level_option :
    isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication source7 = false ∧
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs source7 =
        elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
          types owner inputs source7 ∧
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs source7 = some (coreLO, .word) ∧
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs source7 coreLO .word := by
  have boundary := source7NotGeneric
  let previous : LocalApplicationWithSevenLevelGroupedConditionalExpectedLambdaElaborates
      types owner inputs source7 coreLO .word :=
    .sevenLevelGroupedConditional sevenE.classified sevenE
  let wrapped : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs source7 coreLO .word := .existing boundary previous
  exact ⟨boundary,
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_existing boundary,
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mpr wrapped,
    wrapped⟩

end Tests.FrontendGenericGroupedConditionalProperties
end

section
-- leanmerge: from Solcore.Test.FrontendGroupedExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact one-group expected-lambda adapter. -/
set_option autoImplicit false
namespace Tests.ADR0319SymbolicGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"GroupedExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner : Resolved.DeclarationId := declaration 319
private def foreignOwner : Resolved.DeclarationId := declaration 9319
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
private def file : Syntax.SourceId := ⟨.main, "grouped-expected-lambda.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def body : Syntax.Block :=
  ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr :=
  ⟨span 4, .lambda (span 5)
    ⟨span 6, [⟨span 6, .inferred ⟨span 6, "x"⟩⟩]⟩ none body⟩
private def groupedSource : Syntax.Expr :=
  ⟨span 0, .call (ref 1 "apply")
    ⟨span 2, [⟨span 3, .group argument⟩]⟩⟩
private def core : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private theorem applyElaboration (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 74 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem innerExpectedLambdaElaboration :
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
private theorem groupedElaboration :
    GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs groupedSource core .word :=
  .application (applyElaboration 1) innerExpectedLambdaElaboration
private def ordinaryArgument : Syntax.Expr := ref 20 "ordinary"
private def directSource : Syntax.Expr :=
  ⟨span 17, .call (ref 18 "apply") ⟨span 19, [argument]⟩⟩
private def directCore : Core.Expr := core
private def ordinarySource : Syntax.Expr :=
  ⟨span 21, .call (ref 22 "apply") ⟨span 23, [ordinaryArgument]⟩⟩
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem directExpectedElaboration :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs directSource directCore .word :=
  .application (applyElaboration 18) innerExpectedLambdaElaboration
private theorem ordinaryRecursiveElaboration :
    RecursiveLocalComputationElaborates
      inputs.names inputs.context ordinarySource ordinaryCore .word :=
  .application (applyElaboration 22) (ordinaryElaboration 20)
theorem exact_one_group_contract :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧
    inputs.names[2]? = some ("apply", duplicateId) ∧
    GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs groupedSource core .word ∧
    elaborateGroupedExpectedLambdaArgumentApplication?
      types owner inputs groupedSource = some (core, .word) ∧
    Core.HasType inputs.context.values core .word ∧
    (∃ callSpan argumentsSpan groupSpan callee argument functionCore argumentCore parameterType,
      groupedSource =
        ⟨callSpan, .call callee ⟨argumentsSpan, [⟨groupSpan, .group argument⟩]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType .word) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore) ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs directSource =
      some (directCore, .word) ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs ordinarySource =
      some (ordinaryCore, .word) ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs directSource = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs ordinarySource = none := by
  have checked :=
    elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr groupedElaboration
  have restored :=
    elaborateGroupedExpectedLambdaArgumentApplication?_iff.mp checked
  have directChecked := elaborateExpectedLambdaArgumentApplication?_iff.mpr directExpectedElaboration
  have ordinaryChecked := elaborateRecursiveLocalComputation?_iff.mpr ordinaryRecursiveElaboration
  change
    ([("apply", applyId), ("opaque", opaqueId), ("apply", duplicateId),
      ("flag", flagId), ("ordinary", ordinaryId)][1]?.map Prod.snd = some opaqueId) ∧
    ([⟨"apply", applyId⟩, ⟨"opaque", opaqueId⟩, ⟨"apply", duplicateId⟩,
      ⟨"flag", flagId⟩, ⟨"ordinary", ordinaryId⟩][2]? = some ("apply", duplicateId)) ∧ _
  exact ⟨rfl, rfl, restored, checked, restored.core_hasType, restored.provenance,
    by
      change (if isDirectExpectedLambdaArgumentApplication directSource then
        elaborateExpectedLambdaArgumentApplication? types owner inputs directSource else
        elaborateRecursiveLocalComputation? inputs.names inputs.context directSource) = _
      rw [show isDirectExpectedLambdaArgumentApplication directSource = true by rfl]
      exact directChecked,
    by
      change (if isDirectExpectedLambdaArgumentApplication ordinarySource then
        elaborateExpectedLambdaArgumentApplication? types owner inputs ordinarySource else
        elaborateRecursiveLocalComputation? inputs.names inputs.context ordinarySource) = _
      rw [show isDirectExpectedLambdaArgumentApplication ordinarySource = false by rfl]
      exact ordinaryChecked,
    rfl, rfl⟩
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
theorem independently_executed_grouped_core_application :
    Core.Evaluates environment store core (.word seven) store := by
  exact .apply (.var rfl) .lambda
    (.apply (.var rfl) .word (.var rfl))
private def callGrouped (n : Nat) (callee child : Syntax.Expr) : Syntax.Expr :=
  ⟨span n, .call callee ⟨span (n + 1), [⟨span (n + 2), .group child⟩]⟩⟩
private def doubleGroup := callGrouped 30 (ref 31 "apply") ⟨span 33, .group argument⟩
private def groupedIdentifier := callGrouped 34 (ref 35 "apply") ordinaryArgument
private def groupedTuple := callGrouped 38 (ref 39 "apply")
  ⟨span 41, .tuple ⟨span 42, [argument, ordinaryArgument]⟩⟩
private def groupedConditional := callGrouped 43 (ref 44 "apply")
  ⟨span 46, .conditional (ref 47 "flag") (span 48) argument (span 49) ordinaryArgument⟩
private def innerCall : Syntax.Expr :=
  ⟨span 50, .call (ref 51 "apply") ⟨span 52, [argument]⟩⟩
private def callInsideGroup := callGrouped 53 (ref 54 "ordinary") innerCall
private def badHeaderArgument : Syntax.Expr :=
  ⟨span 57, .lambda (span 58) ⟨span 59, []⟩ none body⟩
private def badHeader := callGrouped 60 (ref 61 "apply") badHeaderArgument
private def badBodyArgument : Syntax.Expr :=
  ⟨span 64, .lambda (span 65)
    ⟨span 66, [⟨span 66, .inferred ⟨span 66, "x"⟩⟩]⟩ none
    ⟨span 67, [⟨span 68, .returnStmt none⟩]⟩⟩
private def badBody := callGrouped 69 (ref 70 "apply") badBodyArgument
private def nonFunction := callGrouped 73 (ref 74 "flag") argument
private def zeroArguments : Syntax.Expr :=
  ⟨span 77, .call (ref 78 "apply") ⟨span 79, []⟩⟩
private def multipleArguments : Syntax.Expr :=
  ⟨span 80, .call (ref 81 "apply") ⟨span 82, [⟨span 83, .group argument⟩, argument]⟩⟩
private def topGroup : Syntax.Expr := ⟨span 84, .group argument⟩
private def returnedLambda : Syntax.Expr :=
  ⟨span 85, .lambda (span 86)
    ⟨span 87, [⟨span 87, .inferred ⟨span 87, "y"⟩⟩]⟩ none
    ⟨span 88, [⟨span 89, .returnStmt (some (ref 90 "y"))⟩]⟩⟩
private def returnBoundaryArgument : Syntax.Expr :=
  ⟨span 91, .lambda (span 92)
    ⟨span 93, [⟨span 93, .inferred ⟨span 93, "x"⟩⟩]⟩ none
    ⟨span 94, [⟨span 95, .returnStmt (some returnedLambda)⟩]⟩⟩
private def returnBoundary := callGrouped 96 (ref 97 "apply") returnBoundaryArgument
private def inferredLetBoundaryArgument : Syntax.Expr :=
  ⟨span 100, .lambda (span 101)
    ⟨span 102, [⟨span 102, .inferred ⟨span 102, "x"⟩⟩]⟩ none
    ⟨span 103, [
      ⟨span 104, .letDecl ⟨span 105, "y"⟩ none (some returnedLambda)⟩,
      ⟨span 106, .returnStmt (some (ref 107 "x"))⟩]⟩⟩
private def inferredLetBoundary := callGrouped 108 (ref 109 "apply") inferredLetBoundaryArgument
private theorem returnBoundaryExpectedAbsent :
    ¬ ∃ core, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs returnBoundaryArgument core functionType := by
  rintro ⟨_, elaboration⟩
  cases elaboration with
  | lambda header _ _ bodyElaboration =>
    cases header
    cases bodyElaboration with
    | expression child =>
      cases child with
      | pure resolution _ _ => cases resolution
private theorem inferredLetBoundaryExpectedAbsent :
    ¬ ∃ core, ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs inferredLetBoundaryArgument core functionType := by
  rintro ⟨_, elaboration⟩
  cases elaboration with
  | lambda header _ _ bodyElaboration =>
    cases header
    cases bodyElaboration with
    | inferred initializerElaboration _ =>
      cases initializerElaboration with
      | pure resolution _ _ => cases resolution
theorem adapter_local_absence_boundaries :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs doubleGroup = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedIdentifier = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedTuple = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedConditional = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs callInsideGroup = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs zeroArguments = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs multipleArguments = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs topGroup = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs returnBoundary = none ∧
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs inferredLetBoundary = none ∧
    ¬ ∃ core type, GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs returnBoundary core type := by
  have r1 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs doubleGroup = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 31)
    simp only [doubleGroup, callGrouped, elaborateGroupedExpectedLambdaArgumentApplication?,
      calleeChecked, bind, Option.bind_some]
    rfl
  have r2 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedIdentifier = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 35)
    simp only [groupedIdentifier, callGrouped,
      elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked, bind, Option.bind_some]
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? ordinaryArgument
    rfl
  have r3 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedTuple = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 39)
    simp only [groupedTuple, callGrouped, elaborateGroupedExpectedLambdaArgumentApplication?,
      calleeChecked, bind, Option.bind_some]
    rfl
  have r4 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedConditional = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 44)
    simp only [groupedConditional, callGrouped,
      elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked, bind, Option.bind_some]
    rfl
  have r5 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs callInsideGroup = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (ordinaryElaboration 54)
    simp only [callInsideGroup, callGrouped,
      elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked, bind, Option.bind_some]
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? innerCall
    rfl
  have r6 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 61)
    simp only [badHeader, callGrouped, elaborateGroupedExpectedLambdaArgumentApplication?,
      calleeChecked, bind, Option.bind_some]
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument
    rfl
  have r7 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 70)
    simp only [badBody, callGrouped, elaborateGroupedExpectedLambdaArgumentApplication?,
      calleeChecked, bind, Option.bind_some]
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBodyArgument
      functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?
    rfl
  have r8 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr flagElaboration
    simp only [nonFunction, callGrouped, elaborateGroupedExpectedLambdaArgumentApplication?,
      calleeChecked, bind, Option.bind_some]
  have r9 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs zeroArguments = none := by rfl
  have r10 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs multipleArguments = none := by rfl
  have r11 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs topGroup = none := by rfl
  have r12 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs returnBoundary = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 97)
    have innerRejected := (elaborateExpectedComputationLambda?_eq_none_iff
      (@elaborateRecursiveLocalComputation?_iff)).mpr returnBoundaryExpectedAbsent
    simp only [returnBoundary, callGrouped,
      elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked, bind, Option.bind_some,
      innerRejected, Option.bind_none]
  have r13 : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs inferredLetBoundary = none := by
    have calleeChecked := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 109)
    have innerRejected := (elaborateExpectedComputationLambda?_eq_none_iff
      (@elaborateRecursiveLocalComputation?_iff)).mpr inferredLetBoundaryExpectedAbsent
    simp only [inferredLetBoundary, callGrouped,
      elaborateGroupedExpectedLambdaArgumentApplication?, calleeChecked, bind, Option.bind_some,
      innerRejected, Option.bind_none]
  refine ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, ?_⟩
  exact elaborateGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mp r12
end Tests.ADR0319SymbolicGroupedExpectedLambdaConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendOneLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedConditionalExpectedLambdaArgumentApplication
/-! Independent parsed consumer for conditional expected-lambda applications. -/
set_option autoImplicit false
namespace Tests.ADR0324ParsedConditionalExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedConditionalExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 324
private def foreignOwner := declaration 9324
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3)) ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5),
      .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 13 "x"
  | .ordinaryLambda => reference file 13 21 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 33 41 "ordinary"
  | .ordinaryLambda => lambdaAt file 24 "x"
  | .lambdaLambda => lambdaAt file 33 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 31 32
  | .ordinaryLambda => range file 22 23
private def conditionalStop : Mode → Nat | .lambdaLambda => 50 | _ => 41
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 1), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 1),
    [⟨range file 6 stop, .conditional (reference file 6 10 "flag") (range file 11 12)
      (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (reference file 6 10 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaElaboration (file : Syntax.SourceFile) (start : Nat) (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word, ⟨range file (start + 6) (start + 17),
      [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaBranchElaborates types owner inputs functionType
      (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaElaboration file 13 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryElaboration file 13 21)
  | lambdaLambda => exact .expected rfl (lambdaElaboration file 13 "x")
private theorem elseElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaBranchElaborates types owner inputs functionType
      (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryElaboration file 33 41)
  | ordinaryLambda => exact .expected rfl (lambdaElaboration file 24 "x")
  | lambdaLambda => exact .expected rfl (lambdaElaboration file 33 "y")
private theorem sourceElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeElaboration file) (flagElaboration file)
    (thenElaboration file _) (elseElaboration file _)
/-- Each exact parsed fixture independently determines its relation and Core endpoint. -/
theorem parsed_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have evidence := sourceElaboration file mode
  exact ⟨evidence, elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr evidence,
    evidence.classified, evidence.core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : List Core.Value := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Both choices execute every branch partition independently without changing the store. -/
theorem independently_executed_conditional_application
    (mode : Mode) (choice : Bool) (opaqueRow duplicateRow wrongRow : Core.Value)
    (initialStore : Core.Store) : Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String
  | .lambdaOrdinary => "apply(flag ? lam(x){return x;} : ordinary)"
  | .ordinaryLambda => "apply(flag ? ordinary : lam(x){return x;})"
  | .lambdaLambda => "apply(flag ? lam(x){return x;} : lam(y){return y;})"
private def modeLabel : Mode → String
  | .lambdaOrdinary => "lambda-ordinary"
  | .ordinaryLambda => "ordinary-lambda"
  | .lambdaLambda => "lambda-lambda"
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
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) (candidate : Syntax.Expr) :
    Option (PLift (candidate = reference file start stop name)) :=
  match shape : candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if same : span = range file start stop ∧ nameSpan = range file start stop ∧
        observed = name then some ⟨by
          rcases same with ⟨rfl, rfl, rfl⟩
          rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match shape : candidate with
  | ⟨lambdaSpan, .lambda keywordSpan
      ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨parameterNameSpan, parameterName⟩⟩]⟩ none
      ⟨bodySpan, [⟨statementSpan, .returnStmt
        (some ⟨resultSpan, .identifier ⟨resultNameSpan, resultName⟩⟩)⟩]⟩⟩ =>
    if same : lambdaSpan = range file start (start + 17) ∧
        keywordSpan = range file start (start + 3) ∧
        parametersSpan = range file (start + 3) (start + 6) ∧
        parameterSpan = range file (start + 4) (start + 5) ∧
        parameterNameSpan = range file (start + 4) (start + 5) ∧
        parameterName = name ∧ bodySpan = range file (start + 6) (start + 17) ∧
        statementSpan = range file (start + 7) (start + 16) ∧
        resultSpan = range file (start + 14) (start + 15) ∧
        resultNameSpan = range file (start + 14) (start + 15) ∧ resultName = name then
      some ⟨by
        rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = source file mode)) :=
  match shape : candidate with
  | ⟨callSpan, .call ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨conditionalSpan, .conditional
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, "flag"⟩⟩ question yes colon no⟩]⟩⟩ =>
    if outer : callSpan = range file 0 (conditionalStop mode + 1) ∧
        calleeSpan = range file 0 5 ∧ calleeNameSpan = range file 0 5 ∧
        argumentsSpan = range file 5 (conditionalStop mode + 1) ∧
        conditionalSpan = range file 6 (conditionalStop mode) ∧
        conditionSpan = range file 6 10 ∧
        conditionNameSpan = range file 6 10 ∧ question = range file 11 12 ∧
        colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let yesEq ← exactLambda? file 13 "x" yes
          let noEq ← exactReference? file 33 41 "ordinary" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
      | .ordinaryLambda => do
          let yesEq ← exactReference? file 13 21 "ordinary" yes
          let noEq ← exactLambda? file 24 "x" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
      | .lambdaLambda => do
          let yesEq ← exactLambda? file 13 "x" yes
          let noEq ← exactLambda? file 33 "y" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
    else none
  | _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0324-{modeLabel mode}.sol" (modeText mode)
  let some parsedEq := exactSource? file mode parsed |
    throw (IO.userError s!"{modeLabel mode}: exact AST or nested spans differ")
  check (isConditionalExpectedLambdaArgumentApplication parsed &&
    elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (core mode, .word))
    s!"{modeLabel mode}: exact checker result changed"
  proof (parsedEq.down ▸ parsed_conditional_static_contract file mode)
  proof (sourceElaboration file mode).provenance
private def rejected (label text : String) (recognized : Bool) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == recognized &&
    (elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone) s!"{label}: conditional boundary changed"
private def verifyFailures : IO Unit := do
  for (label, text) in [
      ("condition-type", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("condition-missing", "apply(missing ? lam(x){return x;} : ordinary)"),
      ("then-header", "apply(flag ? lam(x,y){return x;} : ordinary)"),
      ("else-header", "apply(flag ? ordinary : lam(x,y){return x;})"),
      ("body-type", "apply(flag ? lam(x){return flag;} : ordinary)"),
      ("ordinary-type", "apply(flag ? lam(x){return x;} : wrong)"),
      ("ordinary-missing", "apply(flag ? lam(x){return x;} : missing)"),
      ("nonfunction", "flag(flag ? lam(x){return x;} : ordinary)"),
      ("mixed-grouped", "apply(flag ? lam(x){return x;} : (lam(y){return y;}))"),
      ("mixed-nested", "apply(flag ? lam(x){return x;} : ordinary(lam(y){return y;}))"),
      ("callee-missing", "globalApply(flag ? lam(x){return x;} : ordinary)")] do
    rejected label text true
  for (label, text) in [
      ("grouped-branch", "apply(flag ? (lam(x){return x;}) : ordinary)"),
      ("grouped-conditional", "apply((flag ? lam(x){return x;} : ordinary))"),
      ("nested-call", "apply(flag ? ordinary(lam(x){return x;}) : ordinary)"),
      ("tuple", "apply((lam(x){return x;},ordinary))"),
      ("call", "apply(ordinary(lam(x){return x;}))"), ("zero", "apply()"),
      ("multi", "apply(flag ? lam(x){return x;} : ordinary,ordinary)"),
      ("top", "flag ? lam(x){return x;} : ordinary")] do
    rejected label text false
private def verifyPreservation : IO Unit := do
  let (_, ordinary) ← parseComplete "adr0324-all-ordinary.sol"
    "apply(flag ? ordinary : ordinary)"
  check (!isConditionalExpectedLambdaArgumentApplication ordinary &&
    (elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs ordinary).isNone &&
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs ordinary ==
        some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word))
    "all-ordinary: frozen ADR0322 result changed"
  for (label, text) in [("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))"),
      ("two-groups", "apply(((lam(x){return x;})))")] do
    let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (.apply (.var 0) lambdaCore, .word))
      s!"{label}: frozen ADR0322 result changed"
  for (label, text) in [("three-groups", "apply((((lam(x){return x;}))))"),
      ("seven-groups", "apply((((((((lam(x){return x;}))))))))")] do
    let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs parsed == some (.apply (.var 0) lambdaCore, .word))
      s!"{label}: frozen ADR0323 result changed"
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do
      match Core.runStateful 13 (Core.State.initial (core mode) (environment choice) store) with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError s!"{modeLabel mode}: completed below fuel 14")
      match exactRun : Core.runStateful 14
          (Core.State.initial (core mode) (environment choice) store) with
      | .done value finalStore =>
        check (value == .word seven && finalStore == store)
          s!"{modeLabel mode}: Core result or store changed"
        have actual := Core.runStateful_evaluation_sound exactRun
        have expected : Core.Evaluates (environment choice) store
            (core mode) (.word seven) store := by
          simpa [environment] using independently_executed_conditional_application
            mode choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        proof (Core.evaluation_deterministic actual expected)
      | .outOfFuel _ => throw (IO.userError s!"{modeLabel mode}: no result at fuel 14")
      | .fault _ _ => throw (IO.userError s!"{modeLabel mode}: Core faulted")
  verifyFailures
  verifyPreservation
end Tests.ADR0324ParsedConditionalExpectedLambdaConsumerIndependent
/-- Run every parsed ADR-0324 consumer check. -/
def Tests.adr0324ParsedConditionalExpectedLambdaTests : IO Unit := do
  ADR0324ParsedConditionalExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0324 parsed conditional expected-lambda consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedGenericGroupedConditional
/-!
Parsed consumer coverage for the generic (depth eight or greater) grouped
conditional adapter.  The fixtures pass through the real lexer and parser;
they do not depend on the symbolic fixture module.
-/

set_option autoImplicit false

namespace Tests.FrontendParsedGenericGroupedConditional

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private inductive Mode where
  | lambdaOrdinary
  | ordinaryLambda
  | lambdaLambda

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGenericGroupedConditional", by decide⟩], by decide⟩⟩, index⟩

private def owner := declaration 340
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word

private def inputs : LocalTypeInputs := ⟨
  [⟨"apply", localId 0, .function functionType .word⟩,
   ⟨"flag", localId 1, .bool⟩,
   ⟨"ordinary", localId 2, functionType⟩,
   ⟨"wrong", localId 3, .word⟩],
  by decide⟩

private def types : TypeNameTable := []
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)

private def expectedCore : Mode → Core.Expr
  | .lambdaOrdinary => .apply (.var 0) (.ifE (.var 1) lambdaCore (.var 2))
  | .ordinaryLambda => .apply (.var 0) (.ifE (.var 1) (.var 2) lambdaCore)
  | .lambdaLambda => .apply (.var 0) (.ifE (.var 1) lambdaCore lambdaCore)

private def conditionalText : Mode → String
  | .lambdaOrdinary => "flag ? lam(x){return x;} : ordinary"
  | .ordinaryLambda => "flag ? ordinary : lam(y){return y;}"
  | .lambdaLambda => "flag ? lam(x){return x;} : lam(y){return y;}"

private def label : Mode → String
  | .lambdaOrdinary => "lambda-ordinary"
  | .ordinaryLambda => "ordinary-lambda"
  | .lambdaLambda => "lambda-lambda"

private def repeated (count : Nat) (character : Char) : String :=
  String.ofList (List.replicate count character)

private def groupedCallText (depth : Nat) (body : String) : String :=
  "apply(" ++ repeated depth '(' ++ body ++ repeated depth ')' ++ ")"

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩

private def reference (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) : Syntax.Expr :=
  ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩

private def lambdaAt (file : Syntax.SourceFile) (start : Nat)
    (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6),
      [⟨range file (start + 4) (start + 5),
        .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩
    none
    ⟨range file (start + 6) (start + 17),
      [⟨range file (start + 7) (start + 16),
        .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩

private def conditionalStart (depth : Nat) : Nat := 6 + depth

private def conditionalStop (depth : Nat) : Mode → Nat
  | .lambdaOrdinary | .ordinaryLambda => conditionalStart depth + 35
  | .lambdaLambda => conditionalStart depth + 44

private def conditionalSource (file : Syntax.SourceFile) (depth : Nat) : Mode → Syntax.Expr
  | .lambdaOrdinary =>
      let start := conditionalStart depth
      ⟨range file start (start + 35), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (lambdaAt file (start + 7) "x")
        (range file (start + 25) (start + 26))
        (reference file (start + 27) (start + 35) "ordinary")⟩
  | .ordinaryLambda =>
      let start := conditionalStart depth
      ⟨range file start (start + 35), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (reference file (start + 7) (start + 15) "ordinary")
        (range file (start + 16) (start + 17))
        (lambdaAt file (start + 18) "y")⟩
  | .lambdaLambda =>
      let start := conditionalStart depth
      ⟨range file start (start + 44), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (lambdaAt file (start + 7) "x")
        (range file (start + 25) (start + 26))
        (lambdaAt file (start + 27) "y")⟩

/-- Reconstruct all group spans.  `terminalStop` is the first closing
parenthesis byte; every recursive layer consumes one closing parenthesis. -/
private def groupChain (file : Syntax.SourceFile) (terminalStop opening : Nat) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, terminal => terminal
  | remaining + 1, terminal =>
      ⟨range file opening (terminalStop + remaining + 1), .group
        (groupChain file terminalStop (opening + 1) remaining terminal)⟩

private def expectedSource (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop depth mode
  let total := stop + depth + 1
  ⟨range file 0 total, .call (reference file 0 5 "apply")
    ⟨range file 5 total,
      [groupChain file stop 6 depth (conditionalSource file depth mode)]⟩⟩

private def exactReference? (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) (candidate : Syntax.Expr) :
    Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
      if exact : span = range file start stop ∧
          nameSpan = range file start stop ∧ observed = name then
        some ⟨by rcases exact with ⟨rfl, rfl, rfl⟩; rfl⟩
      else none
  | _ => none

private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨lambdaSpan, .lambda keywordSpan
      ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨nameSpan, observed⟩⟩]⟩ none
      ⟨bodySpan, [⟨statementSpan,
        .returnStmt (some ⟨resultSpan, .identifier ⟨resultNameSpan, result⟩⟩)⟩]⟩⟩ =>
      if exact : lambdaSpan = range file start (start + 17) ∧
          keywordSpan = range file start (start + 3) ∧
          parametersSpan = range file (start + 3) (start + 6) ∧
          parameterSpan = range file (start + 4) (start + 5) ∧
          nameSpan = range file (start + 4) (start + 5) ∧ observed = name ∧
          bodySpan = range file (start + 6) (start + 17) ∧
          statementSpan = range file (start + 7) (start + 16) ∧
          resultSpan = range file (start + 14) (start + 15) ∧
          resultNameSpan = range file (start + 14) (start + 15) ∧
          result = name then
        some ⟨by
          rcases exact with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl⟩
      else none
  | _ => none

private def exactConditional? (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = conditionalSource file depth mode)) :=
  let start := conditionalStart depth
  match mode, candidate with
  | .lambdaOrdinary,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactLambda? file (start + 7) "x" yes
      let noEq ← exactReference? file (start + 27) (start + 35) "ordinary" no
      if exact : conditionalSpan = range file start (start + 35) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 25) (start + 26) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | .ordinaryLambda,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactReference? file (start + 7) (start + 15) "ordinary" yes
      let noEq ← exactLambda? file (start + 18) "y" no
      if exact : conditionalSpan = range file start (start + 35) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 16) (start + 17) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | .lambdaLambda,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactLambda? file (start + 7) "x" yes
      let noEq ← exactLambda? file (start + 27) "y" no
      if exact : conditionalSpan = range file start (start + 44) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 25) (start + 26) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | _, _ => none

private def exactGroupChain? (file : Syntax.SourceFile) (depth : Nat) (mode : Mode)
    (opening : Nat) : (remaining : Nat) → (candidate : Syntax.Expr) →
      Option (PLift (candidate = groupChain file (conditionalStop depth mode)
        opening remaining (conditionalSource file depth mode)))
  | 0, candidate => exactConditional? file depth mode candidate
  | remaining + 1, candidate =>
      match candidate with
      | ⟨groupSpan, .group inner⟩ => do
          let innerEq ← exactGroupChain? file depth mode (opening + 1) remaining inner
          if exact : groupSpan = range file opening
              (conditionalStop depth mode + remaining + 1) then
            some ⟨by rw [exact, innerEq.down]; rfl⟩
          else none
      | _ => none

private def exactExpectedSource? (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = expectedSource file depth mode)) :=
  match candidate with
  | ⟨callSpan, .call callee ⟨argumentsSpan, [grouped]⟩⟩ => do
      let calleeEq ← exactReference? file 0 5 "apply" callee
      let groupedEq ← exactGroupChain? file depth mode 6 depth grouped
      let stop := conditionalStop depth mode
      let total := stop + depth + 1
      if exact : callSpan = range file 0 total ∧
          argumentsSpan = range file 5 total then
        some ⟨by
          rw [calleeEq.down, groupedEq.down]
          rcases exact with ⟨rfl, rfl⟩
          rfl⟩
      else none
  | _ => none

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
      check (next.diagnostics.isEmpty && next.atEnd &&
        parsed.span == Syntax.SourceSpan.fullFile file)
        s!"{path}: parser diagnostics, trailing input, or incomplete span"
      pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")

private theorem applyElaborates (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem flagElaborates (file : Syntax.SourceFile) (depth : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file (conditionalStart depth) (conditionalStart depth + 4) "flag")
      (.var 1) .bool :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "flag"; decide) .head))
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) .head))

private theorem ordinaryElaborates (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 2) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem lambdaElaborates (file : Syntax.SourceFile) (start : Nat)
    (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word,
      ⟨range file (start + 6) (start + 17),
        [⟨range file (start + 7) (start + 16),
          .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩,
      .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))

private def groupSpans (file : Syntax.SourceFile) (terminalStop opening : Nat) :
    Nat → List Syntax.SourceSpan
  | 0 => []
  | remaining + 1 =>
      range file opening (terminalStop + remaining + 1) ::
        groupSpans file terminalStop (opening + 1) remaining

private theorem groupSpans_length (file : Syntax.SourceFile)
    (terminalStop opening remaining : Nat) :
    (groupSpans file terminalStop opening remaining).length = remaining := by
  induction remaining generalizing opening with
  | zero => rfl
  | succ remaining ih => simp [groupSpans, ih]

private theorem groupChainSpine (file : Syntax.SourceFile)
    (terminalStop opening remaining : Nat) (terminal : Syntax.Expr)
    (base : ConditionalGroupSpine terminal [] terminal) :
    ConditionalGroupSpine
      (groupChain file terminalStop opening remaining terminal)
      (groupSpans file terminalStop opening remaining) terminal := by
  induction remaining generalizing opening with
  | zero => simpa [groupChain, groupSpans] using base
  | succ remaining ih =>
      exact .group (ih (opening := opening + 1))

private theorem expectedChildElaborates (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (minimum : 8 ≤ depth) :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs (expectedSource file depth mode) (expectedCore mode) .word := by
  cases mode with
  | lambdaOrdinary =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .lambdaOrdinary) 6 depth
          (conditionalSource file depth .lambdaOrdinary) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 7) "x")
      · exact .ordinary rfl
          (ordinaryElaborates file (conditionalStart depth + 27)
            (conditionalStart depth + 35))
  | ordinaryLambda =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .ordinaryLambda) 6 depth
          (conditionalSource file depth .ordinaryLambda) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .ordinary rfl
          (ordinaryElaborates file (conditionalStart depth + 7)
            (conditionalStart depth + 15))
      · exact .expected rfl
          (lambdaElaborates file (conditionalStart depth + 18) "y")
  | lambdaLambda =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .lambdaLambda) 6 depth
          (conditionalSource file depth .lambdaLambda) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 7) "x")
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 27) "y")

private theorem expectedGenericElaborates (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (minimum : 8 ≤ depth) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file depth mode) (expectedCore mode) .word :=
  let child := expectedChildElaborates file depth mode minimum
  .eightOrMoreGroupedConditional child.classified child

private theorem expectedEightElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 8 .lambdaOrdinary)
      (expectedCore .lambdaOrdinary) .word :=
  expectedGenericElaborates file 8 .lambdaOrdinary (by decide)

private theorem expectedNineElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 9 .ordinaryLambda)
      (expectedCore .ordinaryLambda) .word :=
  expectedGenericElaborates file 9 .ordinaryLambda (by decide)

private theorem expectedSixteenElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 16 .lambdaLambda)
      (expectedCore .lambdaLambda) .word :=
  expectedGenericElaborates file 16 .lambdaLambda (by decide)

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment :=
  [applyValue, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

private def runGenerated
    (runtimeLabel : String) (candidate : Core.Expr) (choice : Bool) : IO Unit := do
  match Core.runStateful 13 (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError s!"{runtimeLabel}: completed with fuel 13")
  match Core.runStateful 14 (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
      check (value == .word seven && finalStore == store)
        s!"{runtimeLabel}: wrong result or mutated store"
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out of fuel at 14")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: Core fault")

private def verifySuccess (depth : Nat) (mode : Mode)
    (staticRelation : ∀ file : Syntax.SourceFile,
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs (expectedSource file depth mode) (expectedCore mode) .word) :
    IO Unit := do
  let (file, parsed) ← parseComplete s!"generic-{depth}-{label mode}.sol"
    (groupedCallText depth (conditionalText mode))
  let some equality := exactExpectedSource? file depth mode parsed |
    throw (IO.userError s!"depth {depth}: exact AST/span equality")
  proof equality.down
  have parsedRelation :
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs parsed (expectedCore mode) .word := by
    rw [equality.down]
    exact staticRelation file
  proof parsedRelation
  proof parsedRelation.core_hasType
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let expected := some (expectedCore mode, .word)
  check (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == expected && wrapped == expected)
    s!"depth {depth}: generic elaboration changed"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    proof
      (elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
        (types := types) (owner := owner) (inputs := inputs) boundary)
  else
    throw (IO.userError s!"depth {depth}: classifier proof")
  match wrapped with
  | some (candidate, .word) =>
      if accepted : wrapped = some (candidate, .word) then
        let relation :=
          elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mp accepted
        proof relation
        proof relation.core_hasType
      else
        throw (IO.userError s!"depth {depth}: correspondence proof")
      for choice in [false, true] do
        runGenerated s!"depth {depth}/{label mode}/{choice}" candidate choice
  | _ => throw (IO.userError s!"depth {depth}: missing generated word Core")

private def verifySevenLevelPreservation : IO Unit := do
  let (_, parsed) ← parseComplete "generic-false-side-depth-7.sol"
    (groupedCallText 7 (conditionalText .lambdaOrdinary))
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let previous :=
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let expected := some (expectedCore .lambdaOrdinary, .word)
  check (!isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child.isNone && previous == expected && wrapped == previous)
    "depth 7: predecessor result was not preserved"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    let route :=
      elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_existing
        (types := types) (owner := owner) (inputs := inputs) boundary
    proof route
    if accepted : previous = some (expectedCore .lambdaOrdinary, .word) then
      let predecessor :=
        elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mp accepted
      let relation : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
          types owner inputs parsed (expectedCore .lambdaOrdinary) .word :=
        .existing boundary predecessor
      proof relation
      proof relation.core_hasType
    else
      throw (IO.userError "depth 7: predecessor correspondence proof")
  else
    throw (IO.userError "depth 7: false-side classifier proof")

private def verifySelectedFailureIsFinal : IO Unit := do
  let (_, parsed) ← parseComplete "generic-selected-failure.sol"
    (groupedCallText 8 "wrong ? lam(x){return x;} : ordinary")
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  check (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child.isNone && wrapped == child && wrapped.isNone)
    "selected semantic failure was not final"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if rejected : child = none then
      let route :=
        elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
          (types := types) (owner := owner) (inputs := inputs) boundary
      proof route
      proof (show wrapped = none by simpa only [wrapped, child] using route.trans rejected)
    else
      throw (IO.userError "selected failure: child rejection proof")
  else
    throw (IO.userError "selected failure: classifier proof")

private def exercise : IO Unit := do
  verifySuccess 8 .lambdaOrdinary expectedEightElaborates
  verifySuccess 9 .ordinaryLambda expectedNineElaborates
  verifySuccess 16 .lambdaLambda expectedSixteenElaborates
  verifySevenLevelPreservation
  verifySelectedFailureIsFinal

end Tests.FrontendParsedGenericGroupedConditional

def Tests.genericGroupedConditionalTests : IO Unit :=
  FrontendParsedGenericGroupedConditional.exercise *>
    IO.println "parsed generic grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedGroupedExpectedLambdaArgumentApplication
/-! Independent parsed consumer for the one-group expected-lambda adapter. -/

set_option autoImplicit false

namespace Tests.ADR0319ParsedGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGroupedExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 319
private def foreignOwner := declaration 9319
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
  ⟨range file 13 24,
    [⟨range file 14 23, .returnStmt (some (reference file 21 22 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 7 24, .lambda (range file 7 10)
    ⟨range file 10 13,
      [⟨range file 11 12, .inferred ⟨range file 11 12, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def groupedSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 26, .call (reference file 0 5 "apply")
    ⟨range file 5 26, [⟨range file 6 25, .group (lambdaArgument file)⟩]⟩⟩

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

private theorem groupedElaboration (file : Syntax.SourceFile) :
    GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs (groupedSource file) expectedCore .word :=
  .application (calleeElaboration file) (lambdaElaboration file)

/-- The parser-shaped grouped source independently constructs the semantic child. -/
theorem parsed_grouped_static_contract (file : Syntax.SourceFile) :
    GroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs (groupedSource file) expectedCore .word ∧
    elaborateGroupedExpectedLambdaArgumentApplication?
      types owner inputs (groupedSource file) = some (expectedCore, .word) ∧
    Core.HasType inputs.context.values expectedCore .word := by
  have evidence := groupedElaboration file
  exact ⟨evidence,
    elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr evidence,
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

/-- Group erasure in the source adapter does not alter the independent Core endpoint. -/
theorem independently_executed_grouped_core_application
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

private def isExactGroupedLambdaApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .group ⟨_, .lambda _ _ _ _⟩⟩]⟩⟩ => true
  | _ => false

private def rejected (label text : String) (recognized : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0319-{label}.sol" text
  check (isExactGroupedLambdaApplication parsed == recognized)
    s!"{label}: exact source-shape boundary changed"
  check (elaborateGroupedExpectedLambdaArgumentApplication?
    types owner inputs parsed).isNone s!"{label}: grouped adapter unexpectedly accepted"

private def verifyGroupedParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0319-grouped.sol"
    "apply((lam(x){return x;}))"
  match shape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨groupSpan, .group
        ⟨lambdaSpan, .lambda keywordSpan
          ⟨parametersSpan, [⟨parameterSpan,
            .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
          ⟨bodySpan, [⟨statementSpan, .returnStmt
            (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 26 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 26 ∧
        groupSpan = range file 6 25 ∧ lambdaSpan = range file 7 24 ∧
        keywordSpan = range file 7 10 ∧ parametersSpan = range file 10 13 ∧
        parameterSpan = range file 11 12 ∧ parameterNameSpan = range file 11 12 ∧
        bodySpan = range file 13 24 ∧ statementSpan = range file 14 23 ∧
        resultSpan = range file 21 22 ∧ resultNameSpan = range file 21 22 then
      have parsedEq : parsed = groupedSource file := by
        rcases spans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (isExactGroupedLambdaApplication parsed &&
        !isDirectExpectedLambdaArgumentApplication parsed &&
        (elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed).isNone &&
        elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs parsed ==
          some (expectedCore, .word)) "grouped: exact disjoint checker result changed"
      proof (show elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs parsed =
          some (expectedCore, .word) from by
        rw [parsedEq]
        exact elaborateGroupedExpectedLambdaArgumentApplication?_iff.mpr
          (groupedElaboration file))
      pure file
    else throw (IO.userError "grouped: exact nested spans differ")
  | _ => throw (IO.userError "grouped: exact parsed AST differs")

private def verifyControls : IO Unit := do
  let (_, direct) ← parseComplete "adr0319-direct-control.sol"
    "apply(lam(x){return x;})"
  check (isDirectExpectedLambdaArgumentApplication direct &&
    (elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs direct).isNone &&
    elaborateLocalApplicationWithExpectedLambda? types owner inputs direct ==
      some (expectedCore, .word)) "direct control changed"
  let (_, ordinary) ← parseComplete "adr0319-ordinary-control.sol" "apply(ordinary)"
  check (!isDirectExpectedLambdaArgumentApplication ordinary &&
    (elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs ordinary).isNone &&
    elaborateLocalApplicationWithExpectedLambda? types owner inputs ordinary ==
      some (ordinaryCore, .word))
    "ordinary control changed"

private def exercise : IO Unit := do
  let file ← verifyGroupedParse
  proof (parsed_grouped_static_contract file)
  verifyControls

  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_grouped_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "double-group" "apply(((lam(x){return x;})))"
  rejected "nested-call" "ordinary(apply((lam(x){return x;})))"
  rejected "call-inside-group" "apply((ordinary(lam(x){return x;})))"
  rejected "tuple" "apply((lam(x){return x;},ordinary))"
  rejected "conditional" "apply((flag ? lam(x){return x;} : ordinary))"
  rejected "bad-body" "apply((lam(x){return flag;}))" true
  rejected "bad-header" "apply((lam(x,y){return x;}))" true
  rejected "nonfunction" "flag((lam(x){return x;}))" true
  rejected "empty-arity" "apply()"
  rejected "many-arity" "apply((lam(x){return x;}),ordinary)"
  rejected "return-boundary" "apply((lam(x){return lam(y){return y;};}))" true
  rejected "inferred-let-boundary"
    "apply((lam(x){let y = lam(z){return z;};return x;}))" true

end Tests.ADR0319ParsedGroupedExpectedLambdaConsumerIndependent

def Tests.adr0319ParsedGroupedExpectedLambdaTests : IO Unit := do
  ADR0319ParsedGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0319 parsed grouped expected-lambda consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOneLevelGroupedConditionalExpectedLambdaArgumentApplication
/-! Independent parsed consumer for one grouped conditional application argument. -/
set_option autoImplicit false
namespace Tests.ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 326
private def foreignOwner := declaration 9326
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
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 14 "x"
  | .ordinaryLambda => reference file 14 22 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 34 42 "ordinary"
  | .ordinaryLambda => lambdaAt file 25 "x"
  | .lambdaLambda => lambdaAt file 34 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 32 33
  | .ordinaryLambda => range file 23 24
private def conditionalStop : Mode → Nat | .lambdaLambda => 51 | _ => 42
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 2), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 2),
    [⟨range file 6 (stop + 1), .group ⟨range file 7 stop, .conditional
      (reference file 7 11 "flag") (range file 12 13) (thenSource file mode)
      (colonRange file mode) (elseSource file mode)⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 7 11 "flag") (.var 3) .bool :=
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
  | lambdaOrdinary => exact .expected rfl (lambdaE file 14 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 14 22)
  | lambdaLambda => exact .expected rfl (lambdaE file 14 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 34 42)
  | ordinaryLambda => exact .expected rfl (lambdaE file 25 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 34 "y")
private theorem sourceE (file : Syntax.SourceFile) (mode : Mode) : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  constructor
  · rfl
  · apply Bool.eq_false_iff.mpr; intro selected
    obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
    cases spine with | group child => cases child
/-- Parsed sources retain the complete new relation, endpoint, partition and provenance. -/
theorem parsed_one_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs (source file mode) =
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have e := sourceE file mode; have old := oldBoundaries file mode
  exact ⟨e, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e,
    e.classified, old.1, old.2,
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing old.1 old.2,
    e.core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Both choices execute every grouped-conditional Core without changing the store. -/
theorem independently_executed_one_group_conditional_core (mode : Mode) (choice : Bool)
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
  | .lambdaOrdinary => "apply((flag ? lam(x){return x;} : ordinary))"
  | .ordinaryLambda => "apply((flag ? ordinary : lam(x){return x;}))"
  | .lambdaLambda => "apply((flag ? lam(x){return x;} : lam(y){return y;}))"
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
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧
        ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧
        pn = range file (start+4) (start+5) ∧ observed = name ∧
        bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧
        rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨gs, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+2) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 (conditionalStop mode+2) ∧ gs = range file 6 (conditionalStop mode+1) ∧
        is = range file 7 (conditionalStop mode) ∧ fs = range file 7 11 ∧ fns = range file 7 11 ∧
        q = range file 12 13 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 14 "x" yes; let n ← exactReference? file 34 42 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 14 22 "ordinary" yes; let n ← exactLambda? file 25 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 14 "x" yes; let n ← exactLambda? file 34 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0326-{label mode}.sol" (modeText mode)
  let some eq := exactSource? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (core mode, .word)) s!"{label mode}: static endpoint"
  proof (eq.down ▸ parsed_one_group_conditional_static_contract file mode)
  proof (sourceE file mode).provenance
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0326-{label}.sol" text
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    (elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone) s!"{label}: recognized failure changed"
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((wrong ? lam(x){return x;} : ordinary))"),
      ("condition-missing", "apply((missing ? lam(x){return x;} : ordinary))"),
      ("header", "apply((flag ? lam(x,y){return x;} : ordinary))"),
      ("body", "apply((flag ? lam(x){return flag;} : ordinary))"),
      ("other-type", "apply((flag ? lam(x){return x;} : wrong))"),
      ("other-missing", "apply((flag ? lam(x){return x;} : missing))"),
      ("nonfunction", "flag((flag ? lam(x){return x;} : ordinary))"),
      ("mixed-grouped", "apply((flag ? lam(x){return x;} : (lam(y){return y;})))"),
      ("mixed-nested", "apply((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))"),
      ("callee-missing", "globalApply((flag ? lam(x){return x;} : ordinary))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0326-{label}.sol" text
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    (elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed == expected) s!"{label}: frozen neighbor changed"
private def verifyPreservation : IO Unit := do
  preserved "ungrouped" "apply(flag ? lam(x){return x;} : ordinary)"
    (some (.apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4)), .word))
  preserved "all-ordinary" "apply((flag ? ordinary : ordinary))"
    (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word))
  preserved "branch-grouped" "apply(flag ? (lam(x){return x;}) : ordinary)" none
  preserved "two-outer" "apply(((flag ? lam(x){return x;} : ordinary)))" none
  preserved "one-lambda-group" "apply((lam(x){return x;}))" (some (.apply (.var 0) lambdaCore, .word))
  preserved "three-lambda-groups" "apply((((lam(x){return x;}))))" (some (.apply (.var 0) lambdaCore, .word))
  preserved "direct-lambda" "apply(lam(x){return x;})" (some (.apply (.var 0) lambdaCore, .word))
  preserved "ordinary" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word))
  preserved "ordinary-depth3" "apply((((ordinary))))" (some (.apply (.var 0) (.var 4), .word))
  for (label, text) in [("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"),
      ("top", "(flag ? lam(x){return x;} : ordinary)"),
      ("tuple", "apply((lam(x){return x;},ordinary))"),
      ("nested-call", "apply(ordinary(lam(x){return x;}))")] do preserved label text none
private def runExact (mode : Mode) (choice : Bool) : IO Unit := do
  match Core.runStateful 13 (Core.State.initial (core mode) (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{label mode}: completed below 14")
  match actual : Core.runStateful 14 (Core.State.initial (core mode) (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{label mode}: result/store"
    have expected : Core.Evaluates (environment choice) store (core mode) (.word seven) store := by
      simpa [environment] using independently_executed_one_group_conditional_core mode choice
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{label mode}: out at 14")
  | .fault _ _ => throw (IO.userError s!"{label mode}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do runExact mode choice
  verifyFailures
  verifyPreservation
end Tests.ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent
/-- Run all parsed ADR-0326 grouped-conditional checks. -/
def Tests.adr0326ParsedOneLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent.exercise
  IO.println "ADR0326 parsed one-level grouped conditional consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedThreeLevelGroupedConditionalExpectedLambdaArgumentApplication
set_option autoImplicit false
namespace Tests.ADR0330ParsedThreeLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedThreeGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 330
private def foreignOwner := declaration 9330
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
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_three_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have old := oldBoundaries file mode
  exact ⟨child, child.classified, old.1, old.2.1, old.2.2.1, old.2.2.2,
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing old.1,
    child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_three_group_conditional_core (mode : Mode) (choice : Bool)
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
  let (file, parsed) ← parseComplete s!"adr0330-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_three_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0330-{label}.sol" text
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
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
  let (file, parsed) ← parseComplete s!"adr0330-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0329 Option changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
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
        have evaluated := independently_executed_three_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_three_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    runExact "immediate-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "one-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "two-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "direct-lambda-control" 10 11 directCore choice (directE choice)
    runExact "finite-group-lambda-control" 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0330ParsedThreeLevelGroupedConditionalConsumerIndependent
def Tests.adr0330ParsedThreeLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0330ParsedThreeLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0330 parsed three-level grouped conditional adapter GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTwoLevelGroupedConditionalExpectedLambdaArgumentApplication
/-! Independent parsed consumer for exactly two grouped conditional application arguments. -/
set_option autoImplicit false
namespace Tests.ADR0328ParsedTwoLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedTwoGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 328
private def foreignOwner := declaration 9328
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
private theorem sourceE (file : Syntax.SourceFile) (mode : Mode) : TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child
/-! Parsed sources retain the complete new relation, endpoint, partitions and provenance. -/
theorem parsed_two_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) =
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have e := sourceE file mode; have old := oldBoundaries file mode
  exact ⟨e, elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e,
    e.classified, old.1, old.2.1, old.2.2,
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing old.1,
    e.core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-! Both choices execute every two-group conditional Core without changing the store. -/
theorem independently_executed_two_group_conditional_core (mode : Mode) (choice : Bool)
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
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧
        ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧
        pn = range file (start+4) (start+5) ∧ observed = name ∧
        bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧
        rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨inner, .group ⟨is, .conditional
        ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+3) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 (conditionalStop mode+3) ∧ outer = range file 6 (conditionalStop mode+2) ∧
        inner = range file 7 (conditionalStop mode+1) ∧ is = range file 8 (conditionalStop mode) ∧
        fs = range file 8 12 ∧ fns = range file 8 12 ∧ q = range file 13 14 ∧ colon = colonRange file mode then
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
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0328-{label mode}.sol" (modeText mode)
  let some eq := exactSource? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  check (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (core mode, .word)) s!"{label mode}: static endpoint"
  proof (eq.down ▸ parsed_two_group_conditional_static_contract file mode)
  proof (sourceE file mode).provenance
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0328-{label}.sol" text
  check (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    (elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone) s!"{label}: recognized failure changed"
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("condition-missing", "apply(((missing ? lam(x){return x;} : ordinary)))"),
      ("header", "apply(((flag ? lam(x,y){return x;} : ordinary)))"),
      ("body", "apply(((flag ? lam(x){return flag;} : ordinary)))"),
      ("other-type", "apply(((flag ? lam(x){return x;} : wrong)))"),
      ("other-missing", "apply(((flag ? lam(x){return x;} : missing)))"),
      ("nonfunction", "flag(((flag ? lam(x){return x;} : ordinary)))"),
      ("mixed-grouped", "apply(((flag ? lam(x){return x;} : (lam(y){return y;}))))"),
      ("mixed-nested", "apply(((flag ? lam(x){return x;} : ordinary(lam(y){return y;}))))"),
      ("callee-missing", "globalApply(((flag ? lam(x){return x;} : ordinary)))")] do rejected label text
private def preserved (label text : String) (oneLevel : Bool)
    (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0328-{label}.sol" text
  let current := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let older := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed
  let groupedConditional := elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  check (!isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    (elaborateTwoLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed).isNone &&
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed == oneLevel && current == expected)
    s!"{label}: exact ADR0328/ADR0327 Option changed"
  if boundary : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    check (groupedConditional == expected) s!"{label}: exact ADR0326 Option changed"
    proof (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_oneLevelGroupedConditional
      (types := types) (owner := owner) (inputs := inputs) (source := parsed) boundary)
  else
    have falseBoundary : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false := by
      cases equality : isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed <;> simp_all
    check (older == expected) s!"{label}: exact ADR0325 Option changed"
    proof (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing
      (types := types) (owner := owner) (inputs := inputs) (source := parsed) falseBoundary)
private def verifyPreservation : IO Unit := do
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))"
    true (some (.apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4)), .word))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)"
    false (some (.apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4)), .word))
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" false none
  preserved "all-ordinary" "apply(((flag ? ordinary : ordinary)))"
    false (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word))
  for (label, text) in [("direct-lambda", "apply(lam(x){return x;})"),
      ("one-lambda-group", "apply((lam(x){return x;}))"),
      ("two-lambda-groups", "apply(((lam(x){return x;})))"),
      ("three-lambda-groups", "apply((((lam(x){return x;}))))")] do
    preserved label text false (some (.apply (.var 0) lambdaCore, .word))
  preserved "ordinary-singleton" "apply(ordinary)" false (some (.apply (.var 0) (.var 4), .word))
  for (label, text) in [("grouped-only", "apply(((flag ? (lam(x){return x;}) : ordinary)))"),
      ("nested-only", "apply(((flag ? ordinary(lam(x){return x;}) : ordinary)))"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"),
      ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text false none
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
        have evaluated := independently_executed_two_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_two_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    runExact "immediate-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "one-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "direct-lambda-control" 10 11 directCore choice (directE choice)
    runExact "finite-group-lambda-control" 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0328ParsedTwoLevelGroupedConditionalConsumerIndependent
/-! Run all parsed ADR-0328 two-level grouped conditional checks. -/
def Tests.adr0328ParsedTwoLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0328ParsedTwoLevelGroupedConditionalConsumerIndependent.exercise
  IO.println "ADR0328 parsed two-level grouped conditional consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTwoLevelGroupedExpectedLambdaArgumentApplication
/-! Independent parsed consumer for the exact two-group expected-lambda adapter. -/

set_option autoImplicit false

namespace Tests.ADR0321ParsedTwoLevelGroupedExpectedLambdaConsumerIndependent

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

/-- The exact parsed source independently constructs, checks and types its evidence. -/
theorem parsed_two_level_static_contract (file : Syntax.SourceFile) :
    TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs (twoLevelSource file) expectedCore .word ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
        types owner inputs (twoLevelSource file) = some (expectedCore, .word) ∧
    Core.HasType inputs.context.values expectedCore .word := by
  have evidence := twoLevelElaboration file
  exact ⟨evidence,
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr evidence,
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
  let (_, parsed) ← parseComplete s!"adr0321-{label}.sol" text
  check (isExactTwoLevelLambdaApplication parsed == recognized)
    s!"{label}: exact source-shape boundary changed"
  check (elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
    types owner inputs parsed).isNone s!"{label}: exact-two adapter unexpectedly accepted"

private def verifyExactParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0321-two-level.sol"
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
        (elaborateLocalApplicationWithGroupedExpectedLambda?
          types owner inputs parsed).isNone &&
        elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed == some (expectedCore, .word))
        "two-level: exact checker result changed"
      proof (show elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed = some (expectedCore, .word) from by
        rw [parsedEq]
        exact elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr
          (twoLevelElaboration file))
      proof (twoLevelElaboration file).provenance
      pure file
    else throw (IO.userError "two-level: exact nested spans differ")
  | _ => throw (IO.userError "two-level: exact parsed AST differs")

private def verifyPreservedPaths : IO Unit := do
  for (label, text) in [
      ("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))")] do
    let (_, parsed) ← parseComplete s!"adr0321-{label}.sol" text
    check ((elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
      elaborateLocalApplicationWithGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word)) s!"{label}: path changed"
  for (label, text) in [
      ("ordinary-0", "apply(ordinary)"), ("ordinary-1", "apply((ordinary))"),
      ("ordinary-2", "apply(((ordinary)))"),
      ("ordinary-3", "apply((((ordinary))))")] do
    let (_, parsed) ← parseComplete s!"adr0321-{label}.sol" text
    check ((elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
      elaborateLocalApplicationWithGroupedExpectedLambda?
        types owner inputs parsed == some (ordinaryCore, .word)) s!"{label}: path changed"
  let (_, deeperLambda) ← parseComplete "adr0321-three-groups.sol"
    "apply((((lam(x){return x;}))))"
  check ((elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
      types owner inputs deeperLambda).isNone &&
    (elaborateLocalApplicationWithGroupedExpectedLambda?
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

end Tests.ADR0321ParsedTwoLevelGroupedExpectedLambdaConsumerIndependent

def Tests.adr0321ParsedTwoLevelGroupedExpectedLambdaTests : IO Unit := do
  ADR0321ParsedTwoLevelGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0321 parsed two-level grouped expected-lambda consumer GREEN"
end

section
-- leanmerge: from Solcore.Test.FrontendThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact three-whole-group conditional adapter. -/
set_option autoImplicit false

namespace Tests.ADR0330ThreeLevelGroupedConditionalSymbolicConsumerIndependent
open Solcore Solcore.Frontend

private def declaration (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ThreeGroupedConditional", by decide⟩], by decide⟩⟩, n⟩
private def owner := declaration 330
private def foreignOwner := declaration 9330
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
private def file : Syntax.SourceId := ⟨.main, "adr0330-symbolic.sol"⟩
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
private def planned (t : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (s : Syntax.Expr) := if isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s
private def ChildProvenance (s : Syntax.Expr) (c : Core.Expr) : Prop := ∃ callSpan argumentsSpan outerGroupSpan middleGroupSpan innerGroupSpan conditionalSpan question colon callee condition yes no functionCore conditionCore yesCore noCore parameterType, s = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan, .group ⟨middleGroupSpan, .group ⟨innerGroupSpan, .group ⟨conditionalSpan, .conditional condition question yes colon no⟩⟩⟩⟩]⟩⟩ ∧ (isImmediateExpectedComputationLambda yes || isImmediateExpectedComputationLambda no) = true ∧ RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore (.function parameterType .word) ∧ RecursiveLocalComputationElaborates inputs.names inputs.context condition conditionCore .bool ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType yes yesCore ∧ ConditionalExpectedLambdaBranchElaborates types owner inputs parameterType no noCore ∧ c = .apply functionCore (.ifE conditionCore yesCore noCore)
private def NewContract (s : Syntax.Expr) (c : Core.Expr) : Prop :=
  isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = true ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication s = false ∧ isConditionalExpectedLambdaArgumentApplication s = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication s = false ∧ isTwoLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isOneLevelGroupedExpectedLambdaArgumentApplication s = false ∧ isDirectExpectedLambdaArgumentApplication s = false ∧ ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs s c .word ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s = some (c, .word) ∧ Core.HasType inputs.context.values c .word ∧ ChildProvenance s c ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs s ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs s = none ∧ planned types owner inputs s = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs s ∧ planned types owner inputs s = some (c, .word)
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
  refine ⟨e.classified, oldBoundary, by cases e; rfl, by cases e; rfl, finite, by cases e; rfl, by cases e; rfl, by cases e; rfl, e, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e, e.core_hasType, e.provenance, current, current.trans oldNone, by simp [planned, e.classified], by simp [planned, e.classified, elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e]⟩

/-! The three selected source partitions retain exact relations, typing and provenance. -/
theorem all_three_three_level_grouped_conditional_partitions_have_exact_semantics :
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
private theorem selectedFailuresFinal : ∀ source ∈ selectedFailures, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none := by
  intro source member; have h := selectedFailuresChild source member
  exact ⟨h.1, h.2, by simp [planned, h.1], by simp [planned, h.1, h.2]⟩

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
  isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs item.1 = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 = item.2 ∧ planned types owner inputs item.1 = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs item.1 ∧ planned types owner inputs item.1 = item.2 ∧ ∀ core type, item.2 = some (core, type) → LocalApplicationWithTwoLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type ∧ ((isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = true ∧ TwoLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs item.1 core type) ∨ (isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication item.1 = false ∧ LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs item.1 core type))
private theorem completeOption {source result} (exact : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = result) (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : CompleteOption (source, result) := by
  have route : planned types owner inputs source = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source := by simp [planned, boundary]
  refine ⟨boundary, rejected, exact, route, route.trans exact, ?_⟩; intro core type observed
  have child := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp (exact.trans observed); exact ⟨child, child.provenance⟩
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

/-! Child Cores stay literal; manual, runner-sound and deterministic execution agree. -/
theorem all_selected_and_control_cores_have_exact_fuel_and_store :
    (∀ choice, Core.Evaluates (environment choice) store coreLO (.word seven) store ∧ Core.Evaluates (environment choice) store coreOL (.word seven) store ∧ Core.Evaluates (environment choice) store coreLL (.word seven) store ∧ Core.Evaluates (environment choice) store allOrdinaryCore (.word seven) store) ∧
    (∀ choice, Core.Evaluates (environment choice) store expectedCore (.word seven) store ∧ Core.Evaluates (environment choice) store ordinaryCore (.word seven) store) ∧
    (∀ choice core, core ∈ [coreLO, coreOL, coreLL, allOrdinaryCore] → exactConditionalFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) ∧
    (∀ choice core, core ∈ [expectedCore, ordinaryCore] → exactLambdaFuel choice core ∧ Core.Evaluates (environment choice) store core (.word seven) store ∧ ∀ value finalStore, Core.Evaluates (environment choice) store core value finalStore → value = .word seven ∧ finalStore = store) := by
  refine ⟨conditionalRuns, lambdaRuns, ?_, ?_⟩
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
private def InheritedFailure (source : Syntax.Expr) : Prop := isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none ∧ planned types owner inputs source = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source ∧ planned types owner inputs source = none
private theorem inherit {source : Syntax.Expr} (current : elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs source = none) (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = false := by rfl) (rejected : elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none := by rfl) : InheritedFailure source := ⟨boundary, rejected, current, by simp [planned, boundary], by simp [planned, boundary, current]⟩
private theorem inheritedAndBoundaryFailuresPreserved : ∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source := by
  intro source member; simp only [inheritedAndBoundaryFailures, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inherit previousTwoConditionalCurrentNone
  all_goals first | exact inherit (currentOldNone rfl previousOneConditionalNone) | exact inherit (currentOldNone rfl previousImmediateConditionalNone) | exact inherit (currentOldNone rfl previousThreeGroupLambdaNone) | exact inherit (currentOldNone rfl previousTwoGroupLambdaNone) | exact inherit (currentOldNone rfl previousOneGroupLambdaNone) | exact inherit (currentOldNone rfl previousDirectLambdaNone) | exact inherit (currentOldNone rfl tuplePreviousNone) | exact inherit (currentOldNone rfl nestedPreviousNone) | exact inherit (currentOldNone rfl returnPreviousNone) | exact inherit (currentOldNone rfl letPreviousNone)

/-! Selected failures are final; every false neighbor retains the complete ADR-0329 Option. -/
theorem selected_failures_and_complete_adr0329_options_are_exact :
    (∀ source ∈ selectedFailures, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication source = true ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source = none ∧ planned types owner inputs source = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs source ∧ planned types owner inputs source = none) ∧
    (∀ item ∈ completeNeighbors, CompleteOption item) ∧
    (∀ source ∈ inheritedAndBoundaryFailures, InheritedFailure source) ∧
    (∀ t o i s, isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false → planned t o i s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s) :=
  ⟨selectedFailuresFinal, completeOptionsExact, inheritedAndBoundaryFailuresPreserved, by intros; simp_all [planned]⟩

end Tests.ADR0330ThreeLevelGroupedConditionalSymbolicConsumerIndependent
end

section
-- leanmerge: from Solcore.Test.FrontendTwoLevelGroupedConditionalExpectedLambdaArgumentApplicationProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendTwoLevelGroupedExpectedLambdaArgumentApplicationProperties
/-! Independent symbolic consumer for the exact two-group expected-lambda adapter. -/
set_option autoImplicit false
namespace Tests.ADR0321SymbolicTwoLevelGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"TwoLevelExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner : Resolved.DeclarationId := declaration 321
private def foreignOwner : Resolved.DeclarationId := declaration 9321
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
  ⟨"opaque", opaqueId, .cell (.function .word .unit)⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩,
  ⟨"ordinary", ordinaryId, functionType⟩], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "two-level-expected-lambda.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def groups (spans : List Nat) (source : Syntax.Expr) : Syntax.Expr :=
  spans.foldr (fun n inner => ⟨span n, .group inner⟩) source
private def callAt (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr :=
  ⟨span n, .call callee ⟨span (n + 1), [argument]⟩⟩
private def twoCall (n : Nat) (callee argument : Syntax.Expr) : Syntax.Expr :=
  callAt n callee ⟨span (n + 2), .group ⟨span (n + 3), .group argument⟩⟩
private def body : Syntax.Block :=
  ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr := ⟨span 4, .lambda (span 5)
  ⟨span 6, [⟨span 6, .inferred ⟨span 6, "x"⟩⟩]⟩ none body⟩
private def source := twoCall 0 (ref 10 "apply") argument
private def core : Core.Expr := .apply (.var 0) (.lambda .word .word (.var 0))
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide)
      (.tail (by change "opaque" ≠ "flag"; decide)
      (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
private theorem groupedOrdinaryElaboration (spans : List Nat) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (groups spans (ref n "ordinary")) (.var 4) functionType := by
  induction spans with
  | nil => exact ordinaryElaboration n
  | cons head tail ih => exact .group ih
private theorem innerElaboration : ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs argument
      (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, body, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))
private theorem sourceElaboration :
    TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core .word :=
  .application (applyElaboration 10) innerElaboration
private def directSource := callAt 20 (ref 22 "apply") argument
private def oneGroupSource := callAt 23 (ref 25 "apply") (groups [26] argument)
private def threeGroupSource := twoCall 27 (ref 31 "apply") (groups [32] argument)
private theorem directOld : elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs directSource = some (core, .word) :=
  elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr
    (.existing rfl (.expected rfl (.application (applyElaboration 22) innerElaboration)))
private theorem oneGroupOld : elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs oneGroupSource = some (core, .word) :=
  elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr
    (.grouped rfl (.application (applyElaboration 25) innerElaboration))
private def ordinaryArgument := ref 40 "ordinary"
private def ordinarySource (n : Nat) (spans : List Nat) :=
  callAt n (ref (n + 4) "apply") (groups spans ordinaryArgument)
private theorem ordinaryOld (n : Nat) (spans : List Nat)
    (outer : isOneLevelGroupedExpectedLambdaArgumentApplication
      (ordinarySource n spans) = false)
    (inner : isDirectExpectedLambdaArgumentApplication (ordinarySource n spans) = false) :
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs
      (ordinarySource n spans) = some (.apply (.var 0) (.var 4), .word) :=
  elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr (.existing outer
    (.ordinary inner (.application (applyElaboration (n + 4))
      (groupedOrdinaryElaboration spans 40))))
private theorem twoApplyRejected (n : Nat) (candidate : Syntax.Expr)
    (rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      types owner inputs candidate functionType = none) :
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs
      (twoCall n (ref (n + 4) "apply") candidate) = none := by
  have callee := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration (n + 4))
  simp only [twoCall, callAt,
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, callee, bind,
    Option.bind_some, rejected, Option.bind_none]
/-- The relation retains both source groups and every executable/static contract without weakening sparse or foreign rows. -/
theorem exact_two_group_contract :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧
    inputs.names[2]? = some ("apply", duplicateId) ∧
    TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs source core .word ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source = some (core, .word) ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source ≠ none ∧
    Core.HasType inputs.context.values core .word ∧
    (∃ callSpan argumentsSpan outerGroupSpan innerGroupSpan callee argument
        functionCore argumentCore parameterType,
      source = ⟨callSpan, .call callee ⟨argumentsSpan, [⟨outerGroupSpan,
        .group ⟨innerGroupSpan, .group argument⟩⟩]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType .word) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs directSource = some (core, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs oneGroupSource = some (core, .word) ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (ordinarySource 50 []) = none ∧ elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (ordinarySource 53 [55]) = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (ordinarySource 56 [58, 59]) = none ∧ elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs (ordinarySource 60 [62, 63, 64]) = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs (ordinarySource 50 []) = some (.apply (.var 0) (.var 4), .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs (ordinarySource 53 [55]) = some (.apply (.var 0) (.var 4), .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs (ordinarySource 56 [58, 59]) = some (.apply (.var 0) (.var 4), .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs (ordinarySource 60 [62, 63, 64]) = some (.apply (.var 0) (.var 4), .word) := by
  have checked := elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mpr sourceElaboration
  have restored := elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_iff.mp checked
  have present : ∃ c t, TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs source c t := ⟨core, .word, restored⟩
  have notNone : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs source ≠ none := by
    intro rejected
    exact (elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mp
      rejected) present
  change (["apply", "opaque", "apply", "flag", "ordinary"].zip
    [applyId, opaqueId, duplicateId, flagId, ordinaryId])[1]?.map Prod.snd =
      some opaqueId ∧ _
  exact ⟨rfl, rfl, restored, checked, notNone, restored.core_hasType,
    restored.provenance, directOld, oneGroupOld, rfl, rfl, (by simpa only [ordinarySource, twoCall, groups, List.foldr] using twoApplyRejected 56 ordinaryArgument (by rfl)), (by simpa only [ordinarySource, twoCall, groups, List.foldr] using twoApplyRejected 60 (groups [64] ordinaryArgument) (by rfl)), ordinaryOld 50 [] rfl rfl,
    ordinaryOld 53 [55] rfl rfl, ordinaryOld 56 [58, 59] rfl rfl,
    ordinaryOld 60 [62, 63, 64] rfl rfl⟩
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
/-- The selected Core term executes independently over opaque values and keeps
the caller's nonempty store literally unchanged. -/
theorem independently_executed_two_group_core_application :
    environment[1]? = some opaqueValue ∧ store[0]? = some opaqueValue ∧
    Core.Evaluates environment store core (.word seven) store := by
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
private theorem expectedAbsent (candidate : Syntax.Expr)
    (absent : ¬ ∃ c, ExpectedComputationLambdaElaborates
      RecursiveLocalComputationElaborates types owner inputs candidate c functionType) :
    elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation?
      types owner inputs candidate functionType = none :=
  (elaborateExpectedComputationLambda?_eq_none_iff
    (@elaborateRecursiveLocalComputation?_iff)).mpr absent
private theorem returnAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs returnArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | expression e => cases e with | pure r _ _ => cases r
private theorem letAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs letArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | inferred e _ => cases e with | pure r _ _ => cases r
private def badHeaderSource := twoCall 116 (ref 120 "apply") badHeaderArgument
private def badBodySource := twoCall 121 (ref 125 "apply") badBodyArgument
private def nonFunctionSource := twoCall 126 (ref 130 "flag") argument
private def unresolvedSource := twoCall 131 (ref 135 "missing") argument
private def nestedSource := callAt 136 (ref 138 "ordinary") source
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
/-- Every selected semantic failure is final, every unsupported shape remains
absent, and the frozen entries retain the neighboring grouping depths. -/
theorem adapter_local_absence_and_preservation_boundaries :
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs directSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs oneGroupSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs threeGroupSource = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs threeGroupSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs badHeaderSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs badBodySource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunctionSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs unresolvedSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs nestedSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs tupleSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs conditionalSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs callSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs zeroArguments = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs multipleArguments = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs topGroups = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs returnSource = none ∧
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs letSource = none ∧
    ¬ ∃ c t, TwoLevelGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs badHeaderSource c t := by
  have bh := twoApplyRejected 116 badHeaderArgument (by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader?
      badHeaderArgument; rfl)
  have bb := twoApplyRejected 121 badBodyArgument (by
    unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader?
      badBodyArgument functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?; rfl)
  have nf : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs
      nonFunctionSource = none := by
    have c := elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration 130)
    simp only [nonFunctionSource, twoCall, callAt,
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, c, bind, Option.bind_some]
  have missing : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs
      unresolvedSource = none := by
    have c : elaborateRecursiveLocalComputation? inputs.names inputs.context
        (ref 135 "missing") = none := by
      have absent : LocalNameTable.lookup? inputs.names "missing" = none := by rfl
      simp only [ref, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
        resolveLocalExpression?, absent, Option.map_none, bind, Option.bind_none]
    simp only [unresolvedSource, twoCall, callAt,
      elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?, c, bind,
      Option.bind_none]
  have tu := twoApplyRejected 139 tupleArgument (by rfl)
  have co := twoApplyRejected 144 conditionalArgument (by rfl)
  have ca := twoApplyRejected 149 innerCall (by rfl)
  have three := twoApplyRejected 27 (groups [32] argument) (by rfl)
  have rb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs
      returnSource = none := by simpa only [returnSource] using (twoApplyRejected 106
        returnArgument (expectedAbsent returnArgument returnAbsent))
  have lb : elaborateTwoLevelGroupedExpectedLambdaArgumentApplication? types owner inputs
      letSource = none := by simpa only [letSource] using (twoApplyRejected 111
        letArgument (expectedAbsent letArgument letAbsent))
  have recursiveThree : elaborateRecursiveLocalComputation? inputs.names inputs.context threeGroupSource = none := by
    have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 31)
    have a : elaborateRecursiveLocalComputation? inputs.names inputs.context ⟨span 29, .group ⟨span 30, .group (groups [32] argument)⟩⟩ = none := by
      simp only [groups, List.foldr, argument, elaborateRecursiveLocalComputation?,
        elaborateLocalExpression?, resolveLocalExpression?, bind, Option.bind_none]
    simp only [threeGroupSource, twoCall, callAt, elaborateRecursiveLocalComputation?, c,
      bind, Option.bind_some, a, Option.bind_none]
  have oldThree : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs
      threeGroupSource = none := by
    rw [elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing (by rfl)]
    change (if isDirectExpectedLambdaArgumentApplication threeGroupSource then elaborateExpectedLambdaArgumentApplication? types owner inputs threeGroupSource else elaborateRecursiveLocalComputation? inputs.names inputs.context threeGroupSource) = none
    rw [show isDirectExpectedLambdaArgumentApplication threeGroupSource = false by rfl]
    exact recursiveThree
  refine ⟨rfl, rfl, three, oldThree, ?_, ?_, nf, missing, rfl, ?_, ?_, ?_, rfl, rfl,
    rfl, rb, lb, ?_⟩
  · simpa only [badHeaderSource] using bh
  · simpa only [badBodySource] using bb
  · simpa only [tupleSource] using tu
  · simpa only [conditionalSource] using co
  · simpa only [callSource] using ca
  · exact elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?_eq_none_iff.mp
      (by simpa only [badHeaderSource] using bh)
end Tests.ADR0321SymbolicTwoLevelGroupedExpectedLambdaConsumerIndependent
end
