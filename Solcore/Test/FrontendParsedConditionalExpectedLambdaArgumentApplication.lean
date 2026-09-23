import Solcore.Frontend.ConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.ThreeOrMoreGroupedExpectedLambdaArgumentApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
/-! Independent parsed consumer for conditional expected-lambda applications. -/
set_option autoImplicit false
namespace Tests.ADR0324ParsedConditionalExpectedLambdaConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedConditionalExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 324
private def foreignOwner := declaration 9324
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3)) ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5),
      .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 13 "x"
  | .ordinaryLambda => reference file 13 21 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 33 41 "ordinary"
  | .ordinaryLambda => lambdaAt file 24 "x"
  | .lambdaLambda => lambdaAt file 33 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 31 32
  | .ordinaryLambda => range file 22 23
private def conditionalStop : Mode → Nat | .lambdaLambda => 50 | _ => 41
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 1), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 1),
    [⟨range file 6 stop, .conditional (reference file 6 10 "flag") (range file 11 12)
      (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names
    inputs.context (reference file 6 10 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide)
      (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaElaboration (file : Syntax.SourceFile) (start : Nat) (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word, ⟨range file (start + 6) (start + 17),
      [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaBranchElaborates types owner inputs functionType
      (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaElaboration file 13 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryElaboration file 13 21)
  | lambdaLambda => exact .expected rfl (lambdaElaboration file 13 "x")
private theorem elseElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaBranchElaborates types owner inputs functionType
      (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryElaboration file 33 41)
  | ordinaryLambda => exact .expected rfl (lambdaElaboration file 24 "x")
  | lambdaLambda => exact .expected rfl (lambdaElaboration file 33 "y")
private theorem sourceElaboration (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeElaboration file) (flagElaboration file)
    (thenElaboration file _) (elseElaboration file _)
/-- Each exact parsed fixture independently determines its relation and Core endpoint. -/
theorem parsed_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have evidence := sourceElaboration file mode
  exact ⟨evidence, elaborateConditionalExpectedLambdaArgumentApplication?_iff.mpr evidence,
    evidence.classified, evidence.core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : List Core.Value := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Both choices execute every branch partition independently without changing the store. -/
theorem independently_executed_conditional_application
    (mode : Mode) (choice : Bool) (opaqueRow duplicateRow wrongRow : Core.Value)
    (initialStore : Core.Store) : Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String
  | .lambdaOrdinary => "apply(flag ? lam(x){return x;} : ordinary)"
  | .ordinaryLambda => "apply(flag ? ordinary : lam(x){return x;})"
  | .lambdaLambda => "apply(flag ? lam(x){return x;} : lam(y){return y;})"
private def modeLabel : Mode → String
  | .lambdaOrdinary => "lambda-ordinary"
  | .ordinaryLambda => "ordinary-lambda"
  | .lambdaLambda => "lambda-lambda"
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
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) (candidate : Syntax.Expr) :
    Option (PLift (candidate = reference file start stop name)) :=
  match shape : candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if same : span = range file start stop ∧ nameSpan = range file start stop ∧
        observed = name then some ⟨by
          rcases same with ⟨rfl, rfl, rfl⟩
          rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match shape : candidate with
  | ⟨lambdaSpan, .lambda keywordSpan
      ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨parameterNameSpan, parameterName⟩⟩]⟩ none
      ⟨bodySpan, [⟨statementSpan, .returnStmt
        (some ⟨resultSpan, .identifier ⟨resultNameSpan, resultName⟩⟩)⟩]⟩⟩ =>
    if same : lambdaSpan = range file start (start + 17) ∧
        keywordSpan = range file start (start + 3) ∧
        parametersSpan = range file (start + 3) (start + 6) ∧
        parameterSpan = range file (start + 4) (start + 5) ∧
        parameterNameSpan = range file (start + 4) (start + 5) ∧
        parameterName = name ∧ bodySpan = range file (start + 6) (start + 17) ∧
        statementSpan = range file (start + 7) (start + 16) ∧
        resultSpan = range file (start + 14) (start + 15) ∧
        resultNameSpan = range file (start + 14) (start + 15) ∧ resultName = name then
      some ⟨by
        rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = source file mode)) :=
  match shape : candidate with
  | ⟨callSpan, .call ⟨calleeSpan, .identifier ⟨calleeNameSpan, "apply"⟩⟩
      ⟨argumentsSpan, [⟨conditionalSpan, .conditional
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, "flag"⟩⟩ question yes colon no⟩]⟩⟩ =>
    if outer : callSpan = range file 0 (conditionalStop mode + 1) ∧
        calleeSpan = range file 0 5 ∧ calleeNameSpan = range file 0 5 ∧
        argumentsSpan = range file 5 (conditionalStop mode + 1) ∧
        conditionalSpan = range file 6 (conditionalStop mode) ∧
        conditionSpan = range file 6 10 ∧
        conditionNameSpan = range file 6 10 ∧ question = range file 11 12 ∧
        colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let yesEq ← exactLambda? file 13 "x" yes
          let noEq ← exactReference? file 33 41 "ordinary" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
      | .ordinaryLambda => do
          let yesEq ← exactReference? file 13 21 "ordinary" yes
          let noEq ← exactLambda? file 24 "x" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
      | .lambdaLambda => do
          let yesEq ← exactLambda? file 13 "x" yes
          let noEq ← exactLambda? file 33 "y" no
          some ⟨by
            rw [yesEq.down, noEq.down]
            rcases outer with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [source, reference, thenSource, elseSource, conditionalStop, colonRange]⟩
    else none
  | _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0324-{modeLabel mode}.sol" (modeText mode)
  let some parsedEq := exactSource? file mode parsed |
    throw (IO.userError s!"{modeLabel mode}: exact AST or nested spans differ")
  check (isConditionalExpectedLambdaArgumentApplication parsed &&
    elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (core mode, .word))
    s!"{modeLabel mode}: exact checker result changed"
  proof (parsedEq.down ▸ parsed_conditional_static_contract file mode)
  proof (sourceElaboration file mode).provenance
private def rejected (label text : String) (recognized : Bool) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == recognized &&
    (elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone) s!"{label}: conditional boundary changed"
private def verifyFailures : IO Unit := do
  for (label, text) in [
      ("condition-type", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("condition-missing", "apply(missing ? lam(x){return x;} : ordinary)"),
      ("then-header", "apply(flag ? lam(x,y){return x;} : ordinary)"),
      ("else-header", "apply(flag ? ordinary : lam(x,y){return x;})"),
      ("body-type", "apply(flag ? lam(x){return flag;} : ordinary)"),
      ("ordinary-type", "apply(flag ? lam(x){return x;} : wrong)"),
      ("ordinary-missing", "apply(flag ? lam(x){return x;} : missing)"),
      ("nonfunction", "flag(flag ? lam(x){return x;} : ordinary)"),
      ("mixed-grouped", "apply(flag ? lam(x){return x;} : (lam(y){return y;}))"),
      ("mixed-nested", "apply(flag ? lam(x){return x;} : ordinary(lam(y){return y;}))"),
      ("callee-missing", "globalApply(flag ? lam(x){return x;} : ordinary)")] do
    rejected label text true
  for (label, text) in [
      ("grouped-branch", "apply(flag ? (lam(x){return x;}) : ordinary)"),
      ("grouped-conditional", "apply((flag ? lam(x){return x;} : ordinary))"),
      ("nested-call", "apply(flag ? ordinary(lam(x){return x;}) : ordinary)"),
      ("tuple", "apply((lam(x){return x;},ordinary))"),
      ("call", "apply(ordinary(lam(x){return x;}))"), ("zero", "apply()"),
      ("multi", "apply(flag ? lam(x){return x;} : ordinary,ordinary)"),
      ("top", "flag ? lam(x){return x;} : ordinary")] do
    rejected label text false
private def verifyPreservation : IO Unit := do
  let (_, ordinary) ← parseComplete "adr0324-all-ordinary.sol"
    "apply(flag ? ordinary : ordinary)"
  check (!isConditionalExpectedLambdaArgumentApplication ordinary &&
    (elaborateConditionalExpectedLambdaArgumentApplication?
      types owner inputs ordinary).isNone &&
    elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
      types owner inputs ordinary ==
        some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word))
    "all-ordinary: frozen ADR0322 result changed"
  for (label, text) in [("direct", "apply(lam(x){return x;})"),
      ("one-group", "apply((lam(x){return x;}))"),
      ("two-groups", "apply(((lam(x){return x;})))")] do
    let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
        types owner inputs parsed == some (.apply (.var 0) lambdaCore, .word))
      s!"{label}: frozen ADR0322 result changed"
  for (label, text) in [("three-groups", "apply((((lam(x){return x;}))))"),
      ("seven-groups", "apply((((((((lam(x){return x;}))))))))")] do
    let (_, parsed) ← parseComplete s!"adr0324-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
        types owner inputs parsed == some (.apply (.var 0) lambdaCore, .word))
      s!"{label}: frozen ADR0323 result changed"
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do
      match Core.runStateful 13 (Core.State.initial (core mode) (environment choice) store) with
      | .outOfFuel _ => pure ()
      | _ => throw (IO.userError s!"{modeLabel mode}: completed below fuel 14")
      match exactRun : Core.runStateful 14
          (Core.State.initial (core mode) (environment choice) store) with
      | .done value finalStore =>
        check (value == .word seven && finalStore == store)
          s!"{modeLabel mode}: Core result or store changed"
        have actual := Core.runStateful_evaluation_sound exactRun
        have expected : Core.Evaluates (environment choice) store
            (core mode) (.word seven) store := by
          simpa [environment] using independently_executed_conditional_application
            mode choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        proof (Core.evaluation_deterministic actual expected)
      | .outOfFuel _ => throw (IO.userError s!"{modeLabel mode}: no result at fuel 14")
      | .fault _ _ => throw (IO.userError s!"{modeLabel mode}: Core faulted")
  verifyFailures
  verifyPreservation
end Tests.ADR0324ParsedConditionalExpectedLambdaConsumerIndependent
/-- Run every parsed ADR-0324 consumer check. -/
def Tests.adr0324ParsedConditionalExpectedLambdaTests : IO Unit := do
  ADR0324ParsedConditionalExpectedLambdaConsumerIndependent.exercise
  IO.println "ADR0324 parsed conditional expected-lambda consumer GREEN"
