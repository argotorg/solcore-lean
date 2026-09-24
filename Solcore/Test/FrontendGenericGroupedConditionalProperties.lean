import Solcore.Frontend.LocalApplication

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
