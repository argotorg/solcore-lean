import Solcore.Frontend.LocalApplication
import Solcore.Core.Eval
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
