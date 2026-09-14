import Solcore.Frontend.LocalApplicationWithExpectedLambda
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

/-! Independent parsed consumer for the source-disjoint ADR0318 application entry. -/

set_option autoImplicit false

namespace Tests.ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedCombinedApplication", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 318
private def foreignOwner := declaration 9318
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
  ⟨range file 12 23,
    [⟨range file 13 22, .returnStmt (some (reference file 20 21 "x"))⟩]⟩
private def lambdaArgument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 23, .lambda (range file 6 9)
    ⟨range file 9 12,
      [⟨range file 10 11, .inferred ⟨range file 10 11, "x"⟩⟩]⟩
    none (lambdaBody file)⟩
private def directSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [lambdaArgument file]⟩⟩
private def ordinarySource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 15, .call (reference file 0 5 "apply")
    ⟨range file 5 15, [reference file 6 14 "ordinary"]⟩⟩

private def directCore : Core.Expr :=
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

private theorem expectedApplicationElaboration (file : Syntax.SourceFile) :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (directSource file) directCore .word :=
  .application (calleeElaboration file) (lambdaElaboration file)

private theorem expectedCombinedElaboration (file : Syntax.SourceFile) :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (directSource file) directCore .word :=
  .expected rfl (expectedApplicationElaboration file)

private theorem ordinaryArgumentElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 6 14 "ordinary") (.var 4) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "opaque" ≠ "ordinary"; decide)
        (.tail (by change "apply" ≠ "ordinary"; decide)
          (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide)
      (.tail (by decide) (.tail (by decide) .head)))))

private theorem ordinaryRecursiveElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (ordinarySource file) ordinaryCore .word :=
  .application (calleeElaboration file) (ordinaryArgumentElaboration file)

private theorem ordinaryCombinedElaboration (file : Syntax.SourceFile) :
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (ordinarySource file) ordinaryCore .word :=
  .ordinary rfl (ordinaryRecursiveElaboration file)

/-- Both source-selected children are constructed before executable correspondence is used. -/
theorem parsed_direct_and_ordinary_static_contract
    (directFile ordinaryFile : Syntax.SourceFile) :
    isDirectExpectedLambdaArgumentApplication (directSource directFile) = true ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (directSource directFile) directCore .word ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs (directSource directFile) = some (directCore, .word) ∧
    Core.HasType inputs.context.values directCore .word ∧
    isDirectExpectedLambdaArgumentApplication (ordinarySource ordinaryFile) = false ∧
    LocalApplicationWithExpectedLambdaElaborates
      types owner inputs (ordinarySource ordinaryFile) ordinaryCore .word ∧
    elaborateLocalApplicationWithExpectedLambda?
      types owner inputs (ordinarySource ordinaryFile) = some (ordinaryCore, .word) ∧
    Core.HasType inputs.context.values ordinaryCore .word := by
  have directEvidence := expectedCombinedElaboration directFile
  have ordinaryEvidence := ordinaryCombinedElaboration ordinaryFile
  have directChecked := elaborateLocalApplicationWithExpectedLambda?_iff.mpr directEvidence
  have ordinaryChecked := elaborateLocalApplicationWithExpectedLambda?_iff.mpr ordinaryEvidence
  exact ⟨rfl, directEvidence, directChecked, directEvidence.core_hasType,
    rfl, ordinaryEvidence, ordinaryChecked, ordinaryEvidence.core_hasType⟩

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

/-- The direct branch's Core endpoint is independent of unrelated rows and store contents. -/
theorem independently_executed_expected_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      directCore (.word seven) initialStore := by
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

private def rejected (label text : String) (direct : Bool := false) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0318-{label}.sol" text
  check (isDirectExpectedLambdaArgumentApplication parsed == direct)
    s!"{label}: source-shape classifier changed"
  if direct then
    check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed).isNone
      s!"{label}: rejected expected branch unexpectedly accepted"
  check (elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed).isNone
    s!"{label}: combined entry unexpectedly accepted"

private def verifyDirectParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0318-direct.sol"
    "apply(lam(x){return x;})"
  match shape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨lambdaSpan, .lambda keywordSpan
        ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨parameterNameSpan, "x"⟩⟩]⟩ none
        ⟨bodySpan, [⟨statementSpan, .returnStmt
          (some ⟨resultSpan, .identifier ⟨resultNameSpan, "x"⟩⟩)⟩]⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 24 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 24 ∧
        lambdaSpan = range file 6 23 ∧ keywordSpan = range file 6 9 ∧
        parametersSpan = range file 9 12 ∧ parameterSpan = range file 10 11 ∧
        parameterNameSpan = range file 10 11 ∧ bodySpan = range file 12 23 ∧
        statementSpan = range file 13 22 ∧ resultSpan = range file 20 21 ∧
        resultNameSpan = range file 20 21 then
      have parsedEq : parsed = directSource file := by
        rcases spans with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed ==
        some (directCore, .word)) "direct: exact checker result changed"
      proof (show elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed =
          some (directCore, .word) from by
        rw [parsedEq]
        exact elaborateLocalApplicationWithExpectedLambda?_iff.mpr
          (expectedCombinedElaboration file))
      pure file
    else throw (IO.userError "direct: exact nested spans differ")
  | _ => throw (IO.userError "direct: exact parsed AST differs")

private def verifyOrdinaryParse : IO Syntax.SourceFile := do
  let (file, parsed) ← parseComplete "adr0318-ordinary.sol" "apply(ordinary)"
  match shape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan,
        [⟨argumentSpan, .identifier ⟨argumentNameSpan, "ordinary"⟩⟩]⟩⟩ =>
    if spans : callSpan = range file 0 15 ∧ calleeSpan = range file 0 5 ∧
        calleeNameSpan = range file 0 5 ∧ argumentsSpan = range file 5 15 ∧
        argumentSpan = range file 6 14 ∧ argumentNameSpan = range file 6 14 then
      have parsedEq : parsed = ordinarySource file := by
        rcases spans with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact shape
      check (!isDirectExpectedLambdaArgumentApplication parsed &&
        elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed ==
          some (ordinaryCore, .word)) "ordinary: disjoint legacy result changed"
      proof (show elaborateLocalApplicationWithExpectedLambda? types owner inputs parsed =
          some (ordinaryCore, .word) from by
        rw [parsedEq]
        exact elaborateLocalApplicationWithExpectedLambda?_iff.mpr
          (ordinaryCombinedElaboration file))
      pure file
    else throw (IO.userError "ordinary: exact nested spans differ")
  | _ => throw (IO.userError "ordinary: exact parsed AST differs")

private def exercise : IO Unit := do
  let directFile ← verifyDirectParse
  let ordinaryFile ← verifyOrdinaryParse
  proof (parsed_direct_and_ordinary_static_contract directFile ordinaryFile)

  match Core.runStateful 10 (Core.State.initial directCore environment store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "Core completed below exact fuel 11")
  match exactRun : Core.runStateful 11 (Core.State.initial directCore environment store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) "Core result or store changed"
    have actual := Core.runStateful_evaluation_sound exactRun
    have expected : Core.Evaluates environment store directCore (.word seven) store := by
      simpa [environment] using independently_executed_expected_core_application
        opaqueValue (.cellRef (.function .unit .word) 31) (.bool false) ordinaryValue store
    proof (Core.evaluation_deterministic actual expected)
  | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
  | .fault _ _ => throw (IO.userError "Core faulted")

  rejected "bad-body" "apply(lam(x){return flag;})" true
  rejected "bad-header" "apply(lam(x,y){return x;})" true
  rejected "grouped-lambda" "apply((lam(x){return x;}))"
  rejected "nested-lambda" "ordinary(apply(lam(x){return x;}))"
  rejected "nonfunction" "flag(lam(x){return x;})" true
  rejected "empty-arity" "apply()"
  rejected "many-arity" "apply(lam(x){return x;},ordinary)"
  rejected "top-level-lambda" "lam(x){return x;}"
  rejected "top-level-identifier" "ordinary"
  rejected "conditional-argument" "apply(flag ? lam(x){return x;} : ordinary)"
  rejected "tuple-argument" "apply((lam(x){return x;},ordinary))"
  rejected "return-boundary" "apply(lam(x){return lam(y){return y;};})" true
  rejected "inferred-let-boundary"
    "apply(lam(x){let y = lam(z){return z;};return x;})" true

end Tests.ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent


def Tests.adr0318LocalApplicationWithExpectedLambdaTests : IO Unit := do
  ADR0318ParsedLocalApplicationWithExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0318 parsed combined application consumer GREEN"
