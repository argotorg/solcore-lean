import Solcore.Frontend.Expected
import Solcore.Core.Eval

/-! Independent symbolic consumers for expected-type lambda arguments. -/

set_option autoImplicit false

namespace Tests.ADR0317ExpectedLambdaArgumentConsumer

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ExpectedLambdaArgument", by decide⟩], by decide⟩⟩, 317⟩
private def foreignOwner : Resolved.DeclarationId := { owner with declarationIndex := 991 }
private def applyId : Resolved.LocalId := ⟨owner, 17⟩
private def opaqueId : Resolved.LocalId := ⟨foreignOwner, 700⟩
private def duplicateId : Resolved.LocalId := ⟨owner, 3⟩
private def flagId : Resolved.LocalId := ⟨foreignOwner, 701⟩

private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[
  ⟨"apply", applyId, .function functionType .word⟩,
  ⟨"opaque", opaqueId, .cell .word⟩,
  ⟨"apply", duplicateId, .unit⟩,
  ⟨"flag", flagId, .bool⟩
], by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "expected-lambda-argument.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr :=
  ⟨span n, .identifier ⟨span (n + 1), name⟩⟩
private def body : Syntax.Block :=
  ⟨span 6, [⟨span 7, .returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr :=
  ⟨span 3, .lambda (span 4)
    ⟨span 5, [⟨span 5, .inferred ⟨span 5, "x"⟩⟩]⟩ none body⟩
private def source : Syntax.Expr :=
  ⟨span 0, .call (ref 1 "apply") ⟨span 2, [argument]⟩⟩
private def core : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

private theorem calleeElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 1 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem argumentElaboration :
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

private theorem independent :
    ExpectedLambdaArgumentApplicationElaborates types owner inputs source core .word :=
  .application calleeElaboration argumentElaboration

theorem checked_literal_application_and_static_boundary :
    ExpectedLambdaArgumentApplicationElaborates types owner inputs source core .word ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs source =
      some (core, .word) ∧
    Core.HasType inputs.context.values core .word ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context source = none := by
  have checked := elaborateExpectedLambdaArgumentApplication?_iff.mpr independent
  have restored := elaborateExpectedLambdaArgumentApplication?_iff.mp checked
  exact ⟨independent, checked, restored.core_hasType, by
    simp [source, argument, elaborateRecursiveLocalComputation?, elaborateLocalExpression?,
      resolveLocalExpression?]⟩

private def nonFunctionCall : Syntax.Expr :=
  ⟨span 23, .call (ref 24 "flag") ⟨span 25, [argument]⟩⟩
private def ordinaryCall : Syntax.Expr :=
  ⟨span 26, .call (ref 1 "apply") ⟨span 27, [ref 28 "flag"]⟩⟩
private def emptyCall : Syntax.Expr :=
  ⟨span 29, .call (ref 1 "apply") ⟨span 30, []⟩⟩
private def manyCall : Syntax.Expr :=
  ⟨span 31, .call (ref 1 "apply") ⟨span 32, [argument, argument]⟩⟩

private theorem flagElaboration :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ref 24 "flag") (.var 3) .bool :=
  .pure
    (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))

theorem unsupported_shapes_remain_exact_absence :
    elaborateExpectedLambdaArgumentApplication? types owner inputs nonFunctionCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs ordinaryCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs emptyCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs manyCall = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs argument = none := by
  have applyChecked := elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration
  have flagChecked := elaborateRecursiveLocalComputation?_iff.mpr flagElaboration
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp only [nonFunctionCall, elaborateExpectedLambdaArgumentApplication?, flagChecked,
      bind, Option.bind_some]
  · simp only [ordinaryCall, elaborateExpectedLambdaArgumentApplication?, applyChecked,
      bind, Option.bind_some]
    rfl

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody []

theorem independently_executed_core_application_keeps_arbitrary_rows
    (opaqueValue duplicateValue flagValue : Core.Value) (store : Core.Store) :
    let environment := [applyValue, opaqueValue, duplicateValue, flagValue]
    Core.Evaluates environment store core (.word seven) store := by
  intro environment
  exact Core.Evaluates.apply
    (Core.Evaluates.var rfl)
    Core.Evaluates.lambda
    (Core.Evaluates.apply
      (Core.Evaluates.var rfl)
      Core.Evaluates.word
      (Core.Evaluates.var rfl))

end Tests.ADR0317ExpectedLambdaArgumentConsumer
