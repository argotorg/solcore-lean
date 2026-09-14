import Solcore.Frontend.LocalApplicationWithGroupedExpectedLambda
import Solcore.Core.Eval
/-! Independent symbolic consumer for the group-first local-application entry. -/
set_option autoImplicit false
namespace Tests.ADR0320SymbolicLocalApplicationWithGroupedExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"GroupFirstApplication",by decide⟩],by decide⟩⟩,index⟩
private def owner : Resolved.DeclarationId := declaration 320
private def foreignOwner : Resolved.DeclarationId := declaration 9320
private def applyId : Resolved.LocalId := ⟨owner, 17⟩
private def opaqueId : Resolved.LocalId := ⟨foreignOwner, 700⟩
private def duplicateId : Resolved.LocalId := ⟨owner, 3⟩
private def flagId : Resolved.LocalId := ⟨foreignOwner, 701⟩
private def ordinaryId : Resolved.LocalId := ⟨owner, 29⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply",applyId,.function functionType .word⟩,
  ⟨"opaque",opaqueId,.cell (.function .word .unit)⟩,⟨"apply",duplicateId,.unit⟩,
  ⟨"flag",flagId,.bool⟩,⟨"ordinary",ordinaryId,functionType⟩],by decide⟩
private def types : TypeNameTable := []
private def file : Syntax.SourceId := ⟨.main, "group-first-application.sol"⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨file, n, n + 1⟩
private def ref (n : Nat) (name : String) : Syntax.Expr := ⟨span n,.identifier ⟨span (n+1),name⟩⟩
private def body : Syntax.Block := ⟨span 6,[⟨span 7,.returnStmt (some (ref 8 "x"))⟩]⟩
private def argument : Syntax.Expr := ⟨span 4,.lambda (span 5)
  ⟨span 6,[⟨span 6,.inferred ⟨span 6,"x"⟩⟩]⟩ none body⟩
private def groupedSource : Syntax.Expr := ⟨span 0,.call (ref 1 "apply")
  ⟨span 2,[⟨span 3,.group argument⟩]⟩⟩
private def directSource : Syntax.Expr := ⟨span 10,.call (ref 11 "apply") ⟨span 12,[argument]⟩⟩
private def ordinaryArgument : Syntax.Expr := ref 14 "ordinary"
private def ordinarySource : Syntax.Expr := ⟨span 15,.call (ref 16 "apply") ⟨span 17,[ordinaryArgument]⟩⟩
private def groupedOrdinarySource : Syntax.Expr := ⟨span 18,.call (ref 19 "apply")
  ⟨span 20,[⟨span 21,.group ordinaryArgument⟩]⟩⟩
private def lambdaCore : Core.Expr := .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem applyElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide)
      (.tail (by change "opaque" ≠ "flag"; decide)
      (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (n : Nat) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (ref n "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide)
      (.tail (by decide) .head)))))
private theorem innerLambdaElaboration : ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs argument
      (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner "x" .word,body,.word,.word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem groupedChild : GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word :=
  .application (applyElaboration 1) innerLambdaElaboration
private theorem directChild : ExpectedLambdaArgumentApplicationElaborates types owner inputs directSource lambdaCore .word :=
  .application (applyElaboration 11) innerLambdaElaboration
private theorem ordinaryChild : RecursiveLocalComputationElaborates inputs.names inputs.context ordinarySource ordinaryCore .word :=
  .application (applyElaboration 16) (ordinaryElaboration 14)
private theorem groupedOrdinaryChild : RecursiveLocalComputationElaborates inputs.names inputs.context groupedOrdinarySource ordinaryCore .word :=
  .application (applyElaboration 19) (.group (ordinaryElaboration 14))
private theorem directExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := .expected rfl directChild
private theorem ordinaryExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := .ordinary rfl ordinaryChild
private theorem groupedOrdinaryExisting : LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word :=
  .ordinary rfl groupedOrdinaryChild
private theorem groupedSelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedSource lambdaCore .word := .grouped rfl groupedChild
private theorem directSelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := .existing rfl directExisting
private theorem ordinarySelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := .existing rfl ordinaryExisting
private theorem groupedOrdinarySelected : LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word :=
  .existing rfl groupedOrdinaryExisting
private theorem groupedProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
    GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word := by
  rcases groupedSelected.provenance with h | h
  · exact h
  · cases h.1
private theorem directProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word := by
  rcases directSelected.provenance with h | h
  · cases h.1
  · exact h
private theorem ordinaryProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word := by
  rcases ordinarySelected.provenance with h | h
  · cases h.1
  · exact h
private theorem groupedOrdinaryProvenance : isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
    LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word := by
  rcases groupedOrdinarySelected.provenance with h | h
  · cases h.1
  · exact h
theorem all_four_source_disjoint_paths_have_exact_semantics :
    inputs.names[1]?.map Prod.snd = some opaqueId ∧ inputs.names[2]? = some ("apply", duplicateId) ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedSource lambdaCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs directSource lambdaCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedSource = some (lambdaCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs directSource = some (lambdaCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs ordinarySource = some (ordinaryCore,.word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedOrdinarySource = some (ordinaryCore,.word) ∧
    Core.HasType inputs.context.values lambdaCore .word ∧ Core.HasType inputs.context.values ordinaryCore .word ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication groupedSource = true ∧
      GroupedExpectedLambdaArgumentApplicationElaborates types owner inputs groupedSource lambdaCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication directSource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs directSource lambdaCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication ordinarySource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs ordinarySource ordinaryCore .word) ∧
    (isOneLevelGroupedExpectedLambdaArgumentApplication groupedOrdinarySource = false ∧
      LocalApplicationWithExpectedLambdaElaborates types owner inputs groupedOrdinarySource ordinaryCore .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedSource =
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs groupedSource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs directSource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs directSource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs ordinarySource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs ordinarySource ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedOrdinarySource =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedOrdinarySource := by
  have g := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedSelected
  have d := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr directSelected
  have o := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr ordinarySelected
  have go := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedOrdinarySelected
  have gr := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp g
  have dr := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp d
  have or := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp o
  have gor := elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mp go
  change (["apply","opaque","apply","flag","ordinary"].zip
    [applyId,opaqueId,duplicateId,flagId,ordinaryId])[1]?.map Prod.snd = some opaqueId ∧ _
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, gr, dr, or, gor, g, d, o, go,
    gr.core_hasType, or.core_hasType, groupedProvenance, directProvenance,
    ordinaryProvenance, groupedOrdinaryProvenance,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl⟩
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
theorem independently_executed_selected_core :
    Core.Evaluates environment store lambdaCore (.word seven) store := by
  exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def groupedCall (n : Nat) (callee child : Syntax.Expr) : Syntax.Expr := ⟨span n,.call callee ⟨span (n+1),[⟨span (n+2),.group child⟩]⟩⟩
private def badHeaderArgument : Syntax.Expr := ⟨span 30,.lambda (span 31) ⟨span 32,[]⟩ none body⟩
private def badHeader := groupedCall 33 (ref 34 "apply") badHeaderArgument
private def badBodyArgument : Syntax.Expr := ⟨span 37,.lambda (span 38)
  ⟨span 39,[⟨span 39,.inferred ⟨span 39,"x"⟩⟩]⟩ none ⟨span 40,[⟨span 41,.returnStmt none⟩]⟩⟩
private def badBody := groupedCall 42 (ref 43 "apply") badBodyArgument
private def nonFunction := groupedCall 46 (ref 47 "flag") argument
private def malformedDirect : Syntax.Expr := ⟨span 50,.call (ref 51 "apply") ⟨span 52,[badHeaderArgument]⟩⟩
private def doubleGroup : Syntax.Expr := groupedCall 53 (ref 54 "apply") ⟨span 56,.group argument⟩
private def innerCall : Syntax.Expr := ⟨span 57,.call (ref 58 "apply") ⟨span 59,[argument]⟩⟩
private def nestedSource : Syntax.Expr := ⟨span 60,.call (ref 61 "ordinary") ⟨span 62,[innerCall]⟩⟩
private def groupedTuple : Syntax.Expr := groupedCall 63 (ref 64 "apply")
  ⟨span 66, .tuple ⟨span 67, [argument, ordinaryArgument]⟩⟩
private def groupedConditional : Syntax.Expr := groupedCall 68 (ref 69 "apply")
  ⟨span 71, .conditional (ref 72 "flag") (span 73) argument (span 74) ordinaryArgument⟩
private def callInsideGroup : Syntax.Expr := groupedCall 75 (ref 76 "ordinary") innerCall
private def zeroArguments : Syntax.Expr := ⟨span 78,.call (ref 79 "apply") ⟨span 80,[]⟩⟩
private def multipleArguments : Syntax.Expr := ⟨span 81,.call (ref 82 "apply") ⟨span 83,[⟨span 84,.group argument⟩,argument]⟩⟩
private def topGroup : Syntax.Expr := ⟨span 85, .group argument⟩
private def returnedLambda : Syntax.Expr := ⟨span 86,.lambda (span 87)
  ⟨span 88,[⟨span 88,.inferred ⟨span 88,"y"⟩⟩]⟩ none ⟨span 89,[⟨span 90,.returnStmt (some (ref 91 "y"))⟩]⟩⟩
private def returnArgument : Syntax.Expr := ⟨span 92,.lambda (span 93)
  ⟨span 94,[⟨span 94,.inferred ⟨span 94,"x"⟩⟩]⟩ none ⟨span 95,[⟨span 96,.returnStmt (some returnedLambda)⟩]⟩⟩
private def returnBoundary := groupedCall 97 (ref 98 "apply") returnArgument
private def inferredLetArgument : Syntax.Expr := ⟨span 101,.lambda (span 102)
  ⟨span 103,[⟨span 103,.inferred ⟨span 103,"x"⟩⟩]⟩ none ⟨span 104,
    [⟨span 105,.letDecl ⟨span 106,"y"⟩ none (some returnedLambda)⟩,⟨span 107,.returnStmt (some (ref 108 "x"))⟩]⟩⟩
private def inferredLetBoundary := groupedCall 109 (ref 110 "apply") inferredLetArgument
private theorem groupedRejected (source : Syntax.Expr) (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = true)
    (child : elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs source = none) : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none :=
  (elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped boundary).trans child
private theorem existingRejected (source : Syntax.Expr) (boundary : isOneLevelGroupedExpectedLambdaArgumentApplication source = false)
    (child : elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none) : elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs source = none :=
  (elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing boundary).trans child
private theorem returnAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs returnArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | expression e => cases e with | pure r _ _ => cases r
private theorem letAbsent : ¬ ∃ c, ExpectedComputationLambdaElaborates
    RecursiveLocalComputationElaborates types owner inputs inferredLetArgument c functionType := by
  rintro ⟨_, h⟩; cases h with | lambda h _ _ b => cases h; cases b with
  | inferred e _ => cases e with | pure r _ _ => cases r
private theorem badHeaderChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 34)
  simp only [badHeader, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument
  rfl
private theorem badBodyChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 43)
  simp only [badBody, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badBodyArgument
    functionType types Core.Ty.isWellFormed elaborateComputationReturnTree?
  rfl
private theorem nonFunctionChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (flagElaboration 47)
  simp only [nonFunction, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
private theorem returnChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs returnBoundary = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 98)
  have x := (elaborateExpectedComputationLambda?_eq_none_iff
    (@elaborateRecursiveLocalComputation?_iff)).mpr returnAbsent
  simp only [returnBoundary, groupedCall, elaborateGroupedExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some, x, Option.bind_none]
private theorem letChild :
    elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs inferredLetBoundary = none := by
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 110)
  have x := (elaborateExpectedComputationLambda?_eq_none_iff
    (@elaborateRecursiveLocalComputation?_iff)).mpr letAbsent
  simp only [inferredLetBoundary, groupedCall,
    elaborateGroupedExpectedLambdaArgumentApplication?, c, bind, Option.bind_some,
    x, Option.bind_none]
private theorem malformedDirectOld :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs malformedDirect = none := by
  change (if isDirectExpectedLambdaArgumentApplication malformedDirect then
    elaborateExpectedLambdaArgumentApplication? types owner inputs malformedDirect else
    elaborateRecursiveLocalComputation? inputs.names inputs.context malformedDirect) = none
  rw [show isDirectExpectedLambdaArgumentApplication malformedDirect = true by rfl]
  have c := elaborateRecursiveLocalComputation?_iff.mpr (applyElaboration 51)
  simp only [malformedDirect, elaborateExpectedLambdaArgumentApplication?, c,
    bind, Option.bind_some]
  unfold elaborateExpectedComputationLambda? declareExpectedUnaryLambdaHeader? badHeaderArgument
  rfl
private theorem oldFalseRejected (source : Syntax.Expr)
    (shape : elaborateLocalApplicationWithExpectedLambda? types owner inputs source =
      if isDirectExpectedLambdaArgumentApplication source then elaborateExpectedLambdaArgumentApplication? types owner inputs source else elaborateRecursiveLocalComputation? inputs.names inputs.context source)
    (boundary : isDirectExpectedLambdaArgumentApplication source = false)
    (child : elaborateRecursiveLocalComputation? inputs.names inputs.context source = none) :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none :=
  shape.trans (by rw [boundary]; exact child)
private theorem falseBoundaryOld : elaborateLocalApplicationWithExpectedLambda? types owner inputs doubleGroup = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs nestedSource = none ∧ elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedTuple = none ∧
    elaborateLocalApplicationWithExpectedLambda? types owner inputs groupedConditional = none ∧ elaborateLocalApplicationWithExpectedLambda? types owner inputs callInsideGroup = none := by
  have h : elaborateRecursiveLocalComputation? inputs.names inputs.context doubleGroup = none ∧ elaborateRecursiveLocalComputation? inputs.names inputs.context nestedSource = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context groupedTuple = none ∧ elaborateRecursiveLocalComputation? inputs.names inputs.context groupedConditional = none ∧
      elaborateRecursiveLocalComputation? inputs.names inputs.context callInsideGroup = none := by
    simp [doubleGroup,nestedSource,groupedTuple,groupedConditional,callInsideGroup,groupedCall,
      innerCall,argument,ordinaryArgument,ref,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]
  rcases h with ⟨d,n,t,c,i⟩
  exact ⟨oldFalseRejected doubleGroup rfl rfl d,oldFalseRejected nestedSource rfl rfl n,
    oldFalseRejected groupedTuple rfl rfl t,oldFalseRejected groupedConditional rfl rfl c,
    oldFalseRejected callInsideGroup rfl rfl i⟩
theorem selected_failures_and_shape_boundaries_are_exact :
    isOneLevelGroupedExpectedLambdaArgumentApplication badHeader = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badHeader = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badHeader ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badHeader = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication badBody = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badBody = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs badBody ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs badBody = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication nonFunction = true ∧ elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nonFunction = elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs nonFunction ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nonFunction = none ∧
    isOneLevelGroupedExpectedLambdaArgumentApplication malformedDirect = false ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs malformedDirect =
      elaborateLocalApplicationWithExpectedLambda? types owner inputs malformedDirect ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs malformedDirect = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs doubleGroup = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs nestedSource = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedTuple = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedConditional = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs callInsideGroup = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs zeroArguments = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs multipleArguments = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs topGroup = none ∧
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs returnBoundary = none ∧ elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs inferredLetBoundary = none ∧
    ¬ ∃ c t, LocalApplicationWithGroupedExpectedLambdaElaborates types owner inputs badHeader c t := by
  rcases falseBoundaryOld with ⟨d, n, t, c, i⟩
  have bh := groupedRejected badHeader rfl badHeaderChild; have bd := groupedRejected badBody rfl badBodyChild
  have nf := groupedRejected nonFunction rfl nonFunctionChild; have md := existingRejected malformedDirect rfl malformedDirectOld
  have dg := existingRejected doubleGroup rfl d; have ne := existingRejected nestedSource rfl n
  have tu := existingRejected groupedTuple rfl t; have co := existingRejected groupedConditional rfl c
  have ci := existingRejected callInsideGroup rfl i; have rb := groupedRejected returnBoundary rfl returnChild
  have lb := groupedRejected inferredLetBoundary rfl letChild
  exact ⟨rfl, badHeaderChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, bh,
    rfl, badBodyChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, bd,
    rfl, nonFunctionChild, elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl, nf, rfl,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl, md,
    dg, ne, tu, co, ci, rfl, rfl, rfl, rb, lb,
    elaborateLocalApplicationWithGroupedExpectedLambda?_eq_none_iff.mp bh⟩
end Tests.ADR0320SymbolicLocalApplicationWithGroupedExpectedLambdaConsumerIndependent
