import Solcore.Frontend.GroupedExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplicationWithExpectedLambda
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

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
