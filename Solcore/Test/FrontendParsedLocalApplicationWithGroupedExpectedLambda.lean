import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

/-! Independent parsed consumer for the group-first ADR-0320 entry. -/

set_option autoImplicit false

namespace Tests.ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGroupFirstApplication", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 320
private def foreignOwner := declaration 9320
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
private def lambdaBody (file : Syntax.SourceFile) (shift : Nat) : Syntax.Block :=
  ⟨range file (12 + shift) (23 + shift),
    [⟨range file (13 + shift) (22 + shift), .returnStmt
      (some (reference file (20 + shift) (21 + shift) "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) (shift : Nat) : Syntax.Expr :=
  ⟨range file (6 + shift) (23 + shift), .lambda (range file (6 + shift) (9 + shift))
    ⟨range file (9 + shift) (12 + shift),
      [⟨range file (10 + shift) (11 + shift), .inferred
        ⟨range file (10 + shift) (11 + shift), "x"⟩⟩]⟩
    none (lambdaBody file shift)⟩
private def directSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [lambdaArgument file 0]⟩⟩
private def groupedSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 26, .call (reference file 0 5 "apply")
    ⟨range file 5 26, [⟨range file 6 25, .group (lambdaArgument file 1)⟩]⟩⟩
private def ordinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 15, .call (reference file 0 5 "apply")
    ⟨range file 5 15, [reference file 6 14 "ordinary"]⟩⟩
private def groupedOrdinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 17, .call (reference file 0 5 "apply")
    ⟨range file 5 17,
      [⟨range file 6 16, .group (reference file 7 15 "ordinary")⟩]⟩⟩

private def expectedCore : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))
private def ordinaryCore : Core.Expr := .apply (.var 0) (.var 4)
private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem lambdaElaboration (file : Syntax.SourceFile) (shift : Nat) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaArgument file shift)
        (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, lambdaBody file shift, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 4) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
        (.tail (by change "apply" ≠ "ordinary"; decide)
          (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))

private theorem groupedEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedSource file) expectedCore .word :=
  .grouped rfl (.application (calleeElaboration file) (lambdaElaboration file 1))
private theorem directEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (directSource file) expectedCore .word :=
  .existing rfl (.expected rfl
    (.application (calleeElaboration file) (lambdaElaboration file 0)))
private theorem ordinaryEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (ordinarySource file) ordinaryCore .word :=
  .existing rfl (.ordinary rfl
    (.application (calleeElaboration file) (ordinaryElaboration file 6 14)))
private theorem groupedOrdinaryEvidence (file : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedOrdinarySource file) ordinaryCore .word :=
  .existing rfl (.ordinary rfl
    (.application (calleeElaboration file) (.group (ordinaryElaboration file 7 15))))

/-- Parsed representatives independently cover all three semantic leaves and grouped ordinary. -/
theorem parsed_three_way_static_contract
    (groupedFile directFile ordinaryFile groupedOrdinaryFile : Syntax.SourceFile) :
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedSource groupedFile) expectedCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedSource groupedFile) = some (expectedCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedSource groupedFile) =
        elaborateGroupedExpectedLambdaArgumentApplication?
          types owner inputs (groupedSource groupedFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (directSource directFile) expectedCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (directSource directFile) = some (expectedCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (directSource directFile) =
        elaborateLocalApplicationWithExpectedLambda? types owner inputs (directSource directFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (ordinarySource ordinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) = some (ordinaryCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) =
        elaborateLocalApplicationWithExpectedLambda? types owner inputs (ordinarySource ordinaryFile) ∧
    LocalApplicationWithGroupedExpectedLambdaElaborates
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) = some (ordinaryCore, .word) ∧
    elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs (groupedOrdinarySource groupedOrdinaryFile) =
        elaborateLocalApplicationWithExpectedLambda?
          types owner inputs (groupedOrdinarySource groupedOrdinaryFile) := by
  have grouped := groupedEvidence groupedFile
  have direct := directEvidence directFile
  have ordinary := ordinaryEvidence ordinaryFile
  have groupedOrdinary := groupedOrdinaryEvidence groupedOrdinaryFile
  exact ⟨grouped, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr grouped,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_grouped rfl,
    direct, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr direct,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    ordinary, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr ordinary,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl,
    groupedOrdinary, elaborateLocalApplicationWithGroupedExpectedLambda?_iff.mpr groupedOrdinary,
    elaborateLocalApplicationWithGroupedExpectedLambda?_of_existing rfl⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool false, ordinaryValue]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The grouped and direct branches share this independently executed Core endpoint. -/
theorem independently_executed_expected_core_application
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
private def parseExact (path text : String) (expected : Syntax.SourceFile → Syntax.Expr) :
    IO (Syntax.SourceFile × Syntax.Expr) := do
  let (file, parsed) ← parseComplete path text
  check (parsed == expected file) s!"{path}: exact AST or nested spans differ"
  pure (file, parsed)

private def rejected (label text : String) (grouped : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0320-{label}.sol" text
  check (isOneLevelGroupedExpectedLambdaArgumentApplication parsed == grouped)
    s!"{label}: group classifier changed"
  if grouped then
    check (elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateGroupedExpectedLambdaArgumentApplication? types owner inputs parsed)
      s!"{label}: grouped branch changed"
    check (elaborateGroupedExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone s!"{label}: grouped child unexpectedly accepted"
  else
    check (elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed)
      s!"{label}: existing branch changed"
  check (elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs parsed).isNone s!"{label}: unified entry unexpectedly accepted"

private def acceptedExisting (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0320-{label}.sol" text
  check (!isOneLevelGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
      some (ordinaryCore, .word)) s!"{label}: existing acceptance changed"

private def exercise : IO Unit := do
  let (groupedFile, groupedParsed) ← parseExact "adr0320-grouped.sol"
    "apply((lam(x){return x;}))" groupedSource
  let (directFile, directParsed) ← parseExact "adr0320-direct.sol"
    "apply(lam(x){return x;})" directSource
  let (ordinaryFile, ordinaryParsed) ← parseExact "adr0320-ordinary.sol"
    "apply(ordinary)" ordinarySource
  let (groupedOrdinaryFile, groupedOrdinaryParsed) ← parseExact
    "adr0320-grouped-ordinary.sol" "apply((ordinary))" groupedOrdinarySource
  proof (parsed_three_way_static_contract
    groupedFile directFile ordinaryFile groupedOrdinaryFile)
  check (isOneLevelGroupedExpectedLambdaArgumentApplication groupedParsed &&
    elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs groupedParsed ==
      some (expectedCore, .word)) "grouped path changed"
  for parsed in [directParsed, ordinaryParsed, groupedOrdinaryParsed] do
    check (!isOneLevelGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithGroupedExpectedLambda? types owner inputs parsed ==
        elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed)
      "existing parsed path changed"
  check (elaborateLocalApplicationWithGroupedExpectedLambda?
    types owner inputs directParsed == some (expectedCore, .word))
    "direct parsed result changed"
  for parsed in [ordinaryParsed, groupedOrdinaryParsed] do
    check (elaborateLocalApplicationWithGroupedExpectedLambda?
      types owner inputs parsed == some (ordinaryCore, .word))
      "ordinary parsed result changed"

  match Core.runStateful 10 (Core.State.initial expectedCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial expectedCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store expectedCore (.word seven) store := by
      simpa [environment] using independently_executed_expected_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  acceptedExisting "double-ordinary-group" "apply(((ordinary)))"
  acceptedExisting "triple-ordinary-group" "apply((((ordinary))))"
  rejected "bad-grouped-body" "apply((lam(x){return flag;}))" true
  rejected "bad-grouped-header" "apply((lam(x,y){return x;}))" true
  rejected "grouped-nonfunction" "flag((lam(x){return x;}))" true
  rejected "bad-direct-body" "apply(lam(x){return flag;})"
  rejected "double-lambda-group" "apply(((lam(x){return x;})))"
  rejected "triple-lambda-group" "apply((((lam(x){return x;}))))"
  rejected "global-callee" "globalApply((lam(x){return x;}))" true
  rejected "nested-call" "ordinary(apply((lam(x){return x;})))"
  rejected "call-inside-group" "apply((ordinary(lam(x){return x;})))"
  rejected "tuple" "apply((lam(x){return x;},ordinary))"
  rejected "conditional" "apply((flag ? lam(x){return x;} : ordinary))"
  rejected "empty-arity" "apply()"
  rejected "many-arity" "apply((lam(x){return x;}),ordinary)"
  rejected "top-group" "(lam(x){return x;})"
  rejected "top-lambda" "lam(x){return x;}"
  rejected "top-identifier" "ordinary"
  rejected "return-boundary" "apply((lam(x){return lam(y){return y;};}))" true
  rejected "inferred-let-boundary"
    "apply((lam(x){let y = lam(z){return z;};return x;}))" true

end Tests.ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent

def Tests.adr0320ParsedLocalApplicationWithGroupedExpectedLambdaTests : IO Unit := do
  ADR0320ParsedLocalApplicationWithGroupedExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0320 parsed group-first application consumer GREEN"
