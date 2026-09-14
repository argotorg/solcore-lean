import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithTwoLevelGroupedExpectedLambda
import Solcore.Frontend.LocalApplicationWithGroupedExpectedLambda
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

/-! Independent parsed consumer for the finite three-or-more group lambda adapter. -/

set_option autoImplicit false

namespace Tests.ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedThreeOrMoreGroupedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 323
private def foreignOwner := declaration 9323
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
  ⟨range file 15 26,
    [⟨range file 16 25, .returnStmt (some (reference file 23 24 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 9 26, .lambda (range file 9 12)
    ⟨range file 12 15,
      [⟨range file 13 14, .inferred ⟨range file 13 14, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def threeGrouped (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 29, .group ⟨range file 7 28, .group
    ⟨range file 8 27, .group (lambdaArgument file)⟩⟩⟩
private def threeLevelSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 30, .call (reference file 0 5 "apply")
    ⟨range file 5 30, [threeGrouped file]⟩⟩

private def expectedCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

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

private theorem threeSpine (file : Syntax.SourceFile) :
    DirectLambdaGroupSpine (threeGrouped file)
      [range file 6 29, range file 7 28, range file 8 27] (lambdaArgument file) :=
  .group (.group (.group .lambda))

private theorem threeLevelElaboration (file : Syntax.SourceFile) :
    ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs (threeLevelSource file) expectedCore .word :=
  .application (threeSpine file) (calleeElaboration file) (lambdaElaboration file)

/-- The exact parsed source retains its ordered spans, checks, classifies and types. -/
theorem parsed_three_or_more_static_contract (file : Syntax.SourceFile) :
    DirectLambdaGroupSpine (threeGrouped file)
        [range file 6 29, range file 7 28, range file 8 27] (lambdaArgument file) ∧
    ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs (threeLevelSource file) expectedCore .word ∧
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs (threeLevelSource file) = some (expectedCore, .word) ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (threeLevelSource file) = true ∧
    Core.HasType inputs.context.values expectedCore .word := by
  have evidence := threeLevelElaboration file
  exact ⟨threeSpine file, evidence,
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr evidence,
    evidence.classified, evidence.core_hasType⟩

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

/-- Erasing every finite source group preserves the independently executed Core endpoint. -/
theorem independently_executed_three_or_more_core_application
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

private def peelObservedGroup? : Option (Syntax.Expr × List Syntax.SourceSpan) →
    Option (Syntax.Expr × List Syntax.SourceSpan)
  | some (⟨span, .group inner⟩, reversed) => some (inner, span :: reversed)
  | _ => none

private def directLambdaGroupSpans? (depth : Nat) (source : Syntax.Expr) :
    Option (List Syntax.SourceSpan) :=
  let state := Nat.rec (motive := fun _ => Option (Syntax.Expr × List Syntax.SourceSpan))
    (some (source, [])) (fun _ state => peelObservedGroup? state) depth
  match state with
  | some (⟨_, .lambda _ _ _ _⟩, reversed) => some reversed.reverse
  | _ => none

private def applicationGroupSpans? (depth : Nat) : Syntax.Expr → Option (List Syntax.SourceSpan)
  | ⟨_, .call _ ⟨_, [grouped]⟩⟩ => directLambdaGroupSpans? depth grouped
  | _ => none

private def rejected (label text : String) (recognized : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0323-{label}.sol" text
  check (isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == recognized)
    s!"{label}: finite-spine source-shape boundary changed"
  check (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
    types owner inputs parsed).isNone s!"{label}: finite-spine adapter unexpectedly accepted"

private def verifyExactParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0323-three-level.sol"
    "apply((((lam(x){return x;}))))"
  match shape : parsed with
  | ⟨callSpan, .call ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨firstSpan, .group ⟨secondSpan, .group
        ⟨thirdSpan, .group ⟨lambdaSpan, .lambda keywordSpan
          ⟨parametersSpan, [⟨parameterSpan,
            .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
          ⟨bodySpan, [⟨statementSpan, .returnStmt
            (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩⟩⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 30 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 30 ∧
        firstSpan = range file 6 29 ∧ secondSpan = range file 7 28 ∧
        thirdSpan = range file 8 27 ∧ lambdaSpan = range file 9 26 ∧
        keywordSpan = range file 9 12 ∧ parametersSpan = range file 12 15 ∧
        parameterSpan = range file 13 14 ∧ parameterNameSpan = range file 13 14 ∧
        bodySpan = range file 15 26 ∧ statementSpan = range file 16 25 ∧
        resultSpan = range file 23 24 ∧ resultNameSpan = range file 23 24 then
      have parsedEq : parsed = threeLevelSource file := by
        rcases spans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
        elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed == some (expectedCore, .word))
        "three-level: exact checker result changed"
      proof (show elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
          types owner inputs parsed = some (expectedCore, .word) from by
        rw [parsedEq]
        exact elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr
          (threeLevelElaboration file))
      proof (threeLevelElaboration file).provenance
      pure file
    else throw (IO.userError "three-level: exact nested spans differ")
  | _ => throw (IO.userError "three-level: exact parsed AST differs")

private def verifyDeeperSpine (label text : String) (depth : Nat) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0323-{label}.sol" text
  let total := 24 + 2 * depth
  let expectedSpans := (List.range depth).map fun index =>
    range file (6 + index) (total - 1 - index)
  check (applicationGroupSpans? depth parsed == some expectedSpans &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (expectedCore, .word))
    s!"{label}: ordered finite-spine checker result changed"

private def verifyDeeperSpines : IO Unit := do
  verifyDeeperSpine "four-groups" "apply(((((lam(x){return x;})))))" 4
  verifyDeeperSpine "seven-groups" "apply((((((((lam(x){return x;}))))))))" 7

private def verifyShallowControls : IO Unit := do
  for (label, text) in [
      ("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))")] do
    let (_, parsed) ← parseComplete s!"adr0323-{label}.sol" text
    check (!isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
      (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs parsed).isNone &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word) &&
      elaborateLocalApplicationWithGroupedExpectedLambda?
        types owner inputs parsed == some (expectedCore, .word)) s!"{label}: path changed"
  let (_, parsed) ← parseComplete "adr0323-two-groups.sol"
    "apply(((lam(x){return x;})))"
  check (!isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    (elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs parsed == some (expectedCore, .word) &&
    elaborateTwoLevelGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (expectedCore, .word)) "two-groups: path changed"

private def exercise : IO Unit := do
  let file ← verifyExactParse
  proof (parsed_three_or_more_static_contract file)
  verifyDeeperSpines
  verifyShallowControls
  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_three_or_more_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "bad-header" "apply((((lam(x,y){return x;}))))" true
  rejected "bad-body" "apply((((lam(x){return flag;}))))" true
  rejected "nonfunction" "flag((((lam(x){return x;}))))" true
  rejected "unresolved" "missing((((lam(x){return x;}))))" true
  rejected "return" "apply((((lam(x){return lam(y){return y;};}))))" true
  rejected "inferred-let"
    "apply((((lam(x){let y = lam(z){return z;};return x;}))))" true
  rejected "non-lambda" "apply((((ordinary))))"
  rejected "nested" "ordinary(apply((((lam(x){return x;})))))"
  rejected "tuple" "apply(((((lam(x){return x;},ordinary)))))"
  rejected "conditional" "apply((((flag ? lam(x){return x;} : ordinary))))"
  rejected "call" "apply((((ordinary(lam(x){return x;})))))"
  rejected "zero" "apply()"
  rejected "multi" "apply((((lam(x){return x;}))),ordinary)"
  rejected "top" "(((lam(x){return x;})))"

end Tests.ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent

def Tests.adr0323ParsedThreeOrMoreGroupedExpectedLambdaTests : IO Unit := do
  ADR0323ParsedThreeOrMoreGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0323 parsed three-or-more grouped expected-lambda consumer GREEN"
