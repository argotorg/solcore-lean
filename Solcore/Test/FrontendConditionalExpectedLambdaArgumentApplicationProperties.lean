import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Core.Eval
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
