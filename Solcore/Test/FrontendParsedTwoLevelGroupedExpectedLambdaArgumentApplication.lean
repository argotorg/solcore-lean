import Solcore.Frontend.TwoLevelGroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithGroupedExpectedLambda
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

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
