import Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Eval
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
