import Solcore.Frontend.ExpectedLambdaArgumentApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

/-! A parsed ADR0317 consumer whose declarative children and Core endpoint are
constructed independently before the executable correspondence is consumed. -/

set_option autoImplicit false

namespace Tests.ADR0317ParsedExpectedLambdaArgumentConsumerIndependent

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedExpectedArgument", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 317
private def foreignOwner := declaration 9317
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
    Syntax.Expr :=
  ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def body (file : Syntax.SourceFile) : Syntax.Block :=
  ⟨range file 12 23,
    [⟨range file 13 22, .returnStmt (some (reference file 20 21 "x"))⟩]⟩
private def argument (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 23, .lambda (range file 6 9)
    ⟨range file 9 12,
      [⟨range file 10 11, .inferred ⟨range file 10 11, "x"⟩⟩]⟩
    none (body file)⟩
private def source (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 24, .call (reference file 0 5 "apply")
    ⟨range file 5 24, [argument file]⟩⟩

private def core : Core.Expr :=
  .apply (.var 0) (.lambda .word .word (.var 0))

private theorem calleeElaboration (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem argumentElaboration (file : Syntax.SourceFile) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (argument file) (.lambda .word .word (.var 0)) functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, body file, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (RecursiveLocalComputationElaborates.pure
        (ResolvesLocalExpression.identifier .head) (Resolved.Lowers.var .head)
        (Resolved.HasType.var .head))

private theorem independentElaboration (file : Syntax.SourceFile) :
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file) core .word :=
  .application (calleeElaboration file) (argumentElaboration file)

private theorem oldCheckerRejects (file : Syntax.SourceFile) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source file) = none := by
  change elaborateRecursiveLocalComputation?
    [("apply", applyId), ("opaque", opaqueId), ("apply", duplicateId),
      ("flag", flagId), ("ordinary", ordinaryId)]
    [(applyId, .function functionType .word), (opaqueId, .cell .word),
      (duplicateId, .unit), (flagId, .bool), (ordinaryId, functionType)]
    (source file) = none
  simp [source, argument, body, reference, elaborateRecursiveLocalComputation?,
    elaborateLocalExpression?, resolveLocalExpression?, functionType,
    LocalNameTable.lookup?]

/-- Static evidence is written independently; only then is the adapter iff used
to recover its exact executable result and Core type. -/
theorem parsed_expected_lambda_argument_static_contract (file : Syntax.SourceFile) :
    inputs.names[2]? = some ("apply", duplicateId) ∧
    inputs.names[1]?.map Prod.snd = some opaqueId ∧
    ExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file) core .word ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source file) = none ∧
    elaborateExpectedLambdaArgumentApplication? types owner inputs (source file) =
      some (core, .word) ∧
    Core.HasType inputs.context.values core .word := by
  have evidence := independentElaboration file
  have checked := elaborateExpectedLambdaArgumentApplication?_iff.mpr evidence
  have restored := elaborateExpectedLambdaArgumentApplication?_iff.mp checked
  exact ⟨rfl, rfl, evidence, oldCheckerRejects file, checked, restored.core_hasType⟩

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def duplicateValue : Core.Value := .cellRef (.function .unit .word) 31
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def applyBody : Core.Expr := .apply (.var 0) (.word seven)
private def applyValue : Core.Value :=
  .closure functionType .word applyBody [opaqueValue, .hostFunction .storageWrite]
private def environment : List (Resolved.LocalId × Core.Value) := [
  (applyId, applyValue), (opaqueId, opaqueValue), (duplicateId, duplicateValue),
  (flagId, .bool false), (ordinaryId, ordinaryValue)]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

/-- The Core result does not depend on the four unrelated rows or on the
initial store, including closures, cells and host values. -/
theorem independently_executed_core_application
    (opaqueRow duplicateRow flagRow ordinaryRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, flagRow, ordinaryRow] initialStore
      core (.word seven) initialStore := by
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

private def rejectedParsed (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0317-{label}.sol" text
  check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed).isNone
    s!"{label}: adapter unexpectedly accepted"

private def exercise : IO Unit := do
  let (file, parsed) ← parseComplete "adr0317-parsed-expected-argument.sol"
    "apply(lam(x){return x;})"
  match parsedShape : parsed with
  | ⟨callSpan, .call
      ⟨calleeSpan, .identifier ⟨calleeNameSpan, calleeName⟩⟩
      ⟨argumentsSpan, [⟨lambdaSpan, .lambda keywordSpan
        ⟨parametersSpan,
          [⟨parameterSpan, .inferred ⟨parameterNameSpan, parameterName⟩⟩]⟩ none
        ⟨bodySpan, [⟨statementSpan, .returnStmt
          (some ⟨resultSpan, .identifier ⟨resultNameSpan, resultName⟩⟩)⟩]⟩⟩]⟩⟩ =>
    if exactSpans : calleeName = "apply" ∧ parameterName = "x" ∧ resultName = "x" ∧
        callSpan = range file 0 24 ∧
        calleeSpan = range file 0 5 ∧ calleeNameSpan = range file 0 5 ∧
        argumentsSpan = range file 5 24 ∧ lambdaSpan = range file 6 23 ∧
        keywordSpan = range file 6 9 ∧ parametersSpan = range file 9 12 ∧
        parameterSpan = range file 10 11 ∧ parameterNameSpan = range file 10 11 ∧
        bodySpan = range file 12 23 ∧ statementSpan = range file 13 22 ∧
        resultSpan = range file 20 21 ∧ resultNameSpan = range file 20 21 then
      have parsedEq : parsed = source file := by
        rcases exactSpans with
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        exact parsedShape
      check ([range file 0 24, range file 0 5, range file 5 24, range file 6 23,
        range file 6 9, range file 9 12, range file 10 11, range file 12 23,
        range file 13 22, range file 20 21].all (fun span => span.isValidFor file))
        "main: exact nested spans are not valid"
      check (elaborateRecursiveLocalComputation? inputs.names inputs.context parsed).isNone
        "main: old recursive checker accepted the literal argument"
      check (elaborateExpectedLambdaArgumentApplication? types owner inputs parsed ==
        some (core, .word)) "main: adapter did not return the literal Core apply"
      proof (show elaborateRecursiveLocalComputation? inputs.names inputs.context parsed = none by
        rw [parsedEq]; exact oldCheckerRejects file)

      match shortRun : Core.runStateful 10
          (Core.State.initial core (environment.map Prod.snd) store) with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError "Core completed below exact fuel 11")
      match exactRun : Core.runStateful 11
          (Core.State.initial core (environment.map Prod.snd) store) with
      | .done value finalStore =>
        check (value == .word seven && finalStore == store)
          "Core exact value or opaque store changed"
        have actual := Core.runStateful_evaluation_sound exactRun
        have expected : Core.Evaluates (environment.map Prod.snd) store core
            (.word seven) store := by
          simpa [environment] using independently_executed_core_application
            opaqueValue duplicateValue (.bool false) ordinaryValue store
        proof (Core.evaluation_deterministic actual expected)
      | .outOfFuel _ => throw (IO.userError "Core did not complete at exact fuel 11")
      | .fault _ _ => throw (IO.userError "Core faulted")

      have evidence := independentElaboration file
      proof evidence
      have checked : elaborateExpectedLambdaArgumentApplication? types owner inputs parsed =
          some (core, .word) := by
        rw [parsedEq]
        exact elaborateExpectedLambdaArgumentApplication?_iff.mpr evidence
      proof checked
      proof (elaborateExpectedLambdaArgumentApplication?_iff.mp checked)
      proof (parsed_expected_lambda_argument_static_contract file)
    else throw (IO.userError "main: exact parsed AST or nested spans differ")
  | _ => throw (IO.userError "main: parsed AST shape differs")

  rejectedParsed "bad-body" "apply(lam(x){return flag;})"
  rejectedParsed "nonfunction" "flag(lam(x){return x;})"
  rejectedParsed "empty-arity" "apply()"
  rejectedParsed "many-arity" "apply(lam(x){return x;},lam(y){return y;})"
  rejectedParsed "top-level" "lam(x){return x;}"

  let (_, ordinary) ← parseComplete "adr0317-ordinary.sol" "apply(ordinary)"
  check (elaborateExpectedLambdaArgumentApplication? types owner inputs ordinary).isNone
    "ordinary: nonliteral argument entered the adapter"
  check (elaborateRecursiveLocalComputation? inputs.names inputs.context ordinary ==
    some (.apply (.var 0) (.var 4), .word))
    "ordinary: existing recursive call path was not preserved"

end Tests.ADR0317ParsedExpectedLambdaArgumentConsumerIndependent

def Tests.adr0317ParsedExpectedLambdaArgumentTests : IO Unit := do
  ADR0317ParsedExpectedLambdaArgumentConsumerIndependent.exercise
  IO.println "ADR0317 parsed expected-lambda argument consumer GREEN"
