import Solcore.Frontend.GroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Eval
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
