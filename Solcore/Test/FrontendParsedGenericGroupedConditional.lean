import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term

/-!
Parsed consumer coverage for the generic (depth eight or greater) grouped
conditional adapter.  The fixtures pass through the real lexer and parser;
they do not depend on the symbolic fixture module.
-/

set_option autoImplicit false

namespace Tests.FrontendParsedGenericGroupedConditional

open Solcore Solcore.Frontend

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()

private inductive Mode where
  | lambdaOrdinary
  | ordinaryLambda
  | lambdaLambda

private def declaration (index : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGenericGroupedConditional", by decide⟩], by decide⟩⟩, index⟩

private def owner := declaration 340
private def localId (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word

private def inputs : LocalTypeInputs := ⟨
  [⟨"apply", localId 0, .function functionType .word⟩,
   ⟨"flag", localId 1, .bool⟩,
   ⟨"ordinary", localId 2, functionType⟩,
   ⟨"wrong", localId 3, .word⟩],
  by decide⟩

private def types : TypeNameTable := []
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)

private def expectedCore : Mode → Core.Expr
  | .lambdaOrdinary => .apply (.var 0) (.ifE (.var 1) lambdaCore (.var 2))
  | .ordinaryLambda => .apply (.var 0) (.ifE (.var 1) (.var 2) lambdaCore)
  | .lambdaLambda => .apply (.var 0) (.ifE (.var 1) lambdaCore lambdaCore)

private def conditionalText : Mode → String
  | .lambdaOrdinary => "flag ? lam(x){return x;} : ordinary"
  | .ordinaryLambda => "flag ? ordinary : lam(y){return y;}"
  | .lambdaLambda => "flag ? lam(x){return x;} : lam(y){return y;}"

private def label : Mode → String
  | .lambdaOrdinary => "lambda-ordinary"
  | .ordinaryLambda => "ordinary-lambda"
  | .lambdaLambda => "lambda-lambda"

private def repeated (count : Nat) (character : Char) : String :=
  String.ofList (List.replicate count character)

private def groupedCallText (depth : Nat) (body : String) : String :=
  "apply(" ++ repeated depth '(' ++ body ++ repeated depth ')' ++ ")"

private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan :=
  ⟨file.id, start, stop⟩

private def reference (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) : Syntax.Expr :=
  ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩

private def lambdaAt (file : Syntax.SourceFile) (start : Nat)
    (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6),
      [⟨range file (start + 4) (start + 5),
        .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩
    none
    ⟨range file (start + 6) (start + 17),
      [⟨range file (start + 7) (start + 16),
        .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩

private def conditionalStart (depth : Nat) : Nat := 6 + depth

private def conditionalStop (depth : Nat) : Mode → Nat
  | .lambdaOrdinary | .ordinaryLambda => conditionalStart depth + 35
  | .lambdaLambda => conditionalStart depth + 44

private def conditionalSource (file : Syntax.SourceFile) (depth : Nat) : Mode → Syntax.Expr
  | .lambdaOrdinary =>
      let start := conditionalStart depth
      ⟨range file start (start + 35), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (lambdaAt file (start + 7) "x")
        (range file (start + 25) (start + 26))
        (reference file (start + 27) (start + 35) "ordinary")⟩
  | .ordinaryLambda =>
      let start := conditionalStart depth
      ⟨range file start (start + 35), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (reference file (start + 7) (start + 15) "ordinary")
        (range file (start + 16) (start + 17))
        (lambdaAt file (start + 18) "y")⟩
  | .lambdaLambda =>
      let start := conditionalStart depth
      ⟨range file start (start + 44), .conditional
        (reference file start (start + 4) "flag")
        (range file (start + 5) (start + 6))
        (lambdaAt file (start + 7) "x")
        (range file (start + 25) (start + 26))
        (lambdaAt file (start + 27) "y")⟩

/-- Reconstruct all group spans.  `terminalStop` is the first closing
parenthesis byte; every recursive layer consumes one closing parenthesis. -/
private def groupChain (file : Syntax.SourceFile) (terminalStop opening : Nat) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, terminal => terminal
  | remaining + 1, terminal =>
      ⟨range file opening (terminalStop + remaining + 1), .group
        (groupChain file terminalStop (opening + 1) remaining terminal)⟩

private def expectedSource (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop depth mode
  let total := stop + depth + 1
  ⟨range file 0 total, .call (reference file 0 5 "apply")
    ⟨range file 5 total,
      [groupChain file stop 6 depth (conditionalSource file depth mode)]⟩⟩

private def exactReference? (file : Syntax.SourceFile) (start stop : Nat)
    (name : String) (candidate : Syntax.Expr) :
    Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
      if exact : span = range file start stop ∧
          nameSpan = range file start stop ∧ observed = name then
        some ⟨by rcases exact with ⟨rfl, rfl, rfl⟩; rfl⟩
      else none
  | _ => none

private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨lambdaSpan, .lambda keywordSpan
      ⟨parametersSpan, [⟨parameterSpan, .inferred ⟨nameSpan, observed⟩⟩]⟩ none
      ⟨bodySpan, [⟨statementSpan,
        .returnStmt (some ⟨resultSpan, .identifier ⟨resultNameSpan, result⟩⟩)⟩]⟩⟩ =>
      if exact : lambdaSpan = range file start (start + 17) ∧
          keywordSpan = range file start (start + 3) ∧
          parametersSpan = range file (start + 3) (start + 6) ∧
          parameterSpan = range file (start + 4) (start + 5) ∧
          nameSpan = range file (start + 4) (start + 5) ∧ observed = name ∧
          bodySpan = range file (start + 6) (start + 17) ∧
          statementSpan = range file (start + 7) (start + 16) ∧
          resultSpan = range file (start + 14) (start + 15) ∧
          resultNameSpan = range file (start + 14) (start + 15) ∧
          result = name then
        some ⟨by
          rcases exact with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl⟩
      else none
  | _ => none

private def exactConditional? (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = conditionalSource file depth mode)) :=
  let start := conditionalStart depth
  match mode, candidate with
  | .lambdaOrdinary,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactLambda? file (start + 7) "x" yes
      let noEq ← exactReference? file (start + 27) (start + 35) "ordinary" no
      if exact : conditionalSpan = range file start (start + 35) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 25) (start + 26) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | .ordinaryLambda,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactReference? file (start + 7) (start + 15) "ordinary" yes
      let noEq ← exactLambda? file (start + 18) "y" no
      if exact : conditionalSpan = range file start (start + 35) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 16) (start + 17) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | .lambdaLambda,
      ⟨conditionalSpan, .conditional condition question yes colon no⟩ => do
      let conditionEq ← exactReference? file start (start + 4) "flag" condition
      let yesEq ← exactLambda? file (start + 7) "x" yes
      let noEq ← exactLambda? file (start + 27) "y" no
      if exact : conditionalSpan = range file start (start + 44) ∧
          question = range file (start + 5) (start + 6) ∧
          colon = range file (start + 25) (start + 26) then
        some ⟨by
          rw [conditionEq.down, yesEq.down, noEq.down]
          rcases exact with ⟨rfl, rfl, rfl⟩
          rfl⟩
      else none
  | _, _ => none

private def exactGroupChain? (file : Syntax.SourceFile) (depth : Nat) (mode : Mode)
    (opening : Nat) : (remaining : Nat) → (candidate : Syntax.Expr) →
      Option (PLift (candidate = groupChain file (conditionalStop depth mode)
        opening remaining (conditionalSource file depth mode)))
  | 0, candidate => exactConditional? file depth mode candidate
  | remaining + 1, candidate =>
      match candidate with
      | ⟨groupSpan, .group inner⟩ => do
          let innerEq ← exactGroupChain? file depth mode (opening + 1) remaining inner
          if exact : groupSpan = range file opening
              (conditionalStop depth mode + remaining + 1) then
            some ⟨by rw [exact, innerEq.down]; rfl⟩
          else none
      | _ => none

private def exactExpectedSource? (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (candidate : Syntax.Expr) :
    Option (PLift (candidate = expectedSource file depth mode)) :=
  match candidate with
  | ⟨callSpan, .call callee ⟨argumentsSpan, [grouped]⟩⟩ => do
      let calleeEq ← exactReference? file 0 5 "apply" callee
      let groupedEq ← exactGroupChain? file depth mode 6 depth grouped
      let stop := conditionalStop depth mode
      let total := stop + depth + 1
      if exact : callSpan = range file 0 total ∧
          argumentsSpan = range file 5 total then
        some ⟨by
          rw [calleeEq.down, groupedEq.down]
          rcases exact with ⟨rfl, rfl⟩
          rfl⟩
      else none
  | _ => none

private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file |
    throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
      check (next.diagnostics.isEmpty && next.atEnd &&
        parsed.span == Syntax.SourceSpan.fullFile file)
        s!"{path}: parser diagnostics, trailing input, or incomplete span"
      pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")

private theorem applyElaborates (file : Syntax.SourceFile) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)

private theorem flagElaborates (file : Syntax.SourceFile) (depth : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file (conditionalStart depth) (conditionalStart depth + 4) "flag")
      (.var 1) .bool :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "flag"; decide) .head))
    (.var (.tail (by decide) .head))
    (.var (.tail (by decide) .head))

private theorem ordinaryElaborates (file : Syntax.SourceFile) (start stop : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context
      (reference file start stop "ordinary") (.var 2) functionType :=
  .pure
    (.identifier (.tail (by change "apply" ≠ "ordinary"; decide)
      (.tail (by change "flag" ≠ "ordinary"; decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))

private theorem lambdaElaborates (file : Syntax.SourceFile) (start : Nat)
    (name : String) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
      types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner name .word,
      ⟨range file (start + 6) (start + 17),
        [⟨range file (start + 7) (start + 16),
          .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩,
      .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))

private def groupSpans (file : Syntax.SourceFile) (terminalStop opening : Nat) :
    Nat → List Syntax.SourceSpan
  | 0 => []
  | remaining + 1 =>
      range file opening (terminalStop + remaining + 1) ::
        groupSpans file terminalStop (opening + 1) remaining

private theorem groupSpans_length (file : Syntax.SourceFile)
    (terminalStop opening remaining : Nat) :
    (groupSpans file terminalStop opening remaining).length = remaining := by
  induction remaining generalizing opening with
  | zero => rfl
  | succ remaining ih => simp [groupSpans, ih]

private theorem groupChainSpine (file : Syntax.SourceFile)
    (terminalStop opening remaining : Nat) (terminal : Syntax.Expr)
    (base : ConditionalGroupSpine terminal [] terminal) :
    ConditionalGroupSpine
      (groupChain file terminalStop opening remaining terminal)
      (groupSpans file terminalStop opening remaining) terminal := by
  induction remaining generalizing opening with
  | zero => simpa [groupChain, groupSpans] using base
  | succ remaining ih =>
      exact .group (ih (opening := opening + 1))

private theorem expectedChildElaborates (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (minimum : 8 ≤ depth) :
    EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates
      types owner inputs (expectedSource file depth mode) (expectedCore mode) .word := by
  cases mode with
  | lambdaOrdinary =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .lambdaOrdinary) 6 depth
          (conditionalSource file depth .lambdaOrdinary) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 7) "x")
      · exact .ordinary rfl
          (ordinaryElaborates file (conditionalStart depth + 27)
            (conditionalStart depth + 35))
  | ordinaryLambda =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .ordinaryLambda) 6 depth
          (conditionalSource file depth .ordinaryLambda) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .ordinary rfl
          (ordinaryElaborates file (conditionalStart depth + 7)
            (conditionalStart depth + 15))
      · exact .expected rfl
          (lambdaElaborates file (conditionalStart depth + 18) "y")
  | lambdaLambda =>
      apply EightOrMoreGroupedConditionalExpectedLambdaArgumentApplicationElaborates.application
        (groupChainSpine file (conditionalStop depth .lambdaLambda) 6 depth
          (conditionalSource file depth .lambdaLambda) .conditional)
      · simpa [groupSpans_length] using minimum
      · rfl
      · exact applyElaborates file
      · exact flagElaborates file depth
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 7) "x")
      · exact .expected rfl (lambdaElaborates file (conditionalStart depth + 27) "y")

private theorem expectedGenericElaborates (file : Syntax.SourceFile) (depth : Nat)
    (mode : Mode) (minimum : 8 ≤ depth) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file depth mode) (expectedCore mode) .word :=
  let child := expectedChildElaborates file depth mode minimum
  .eightOrMoreGroupedConditional child.classified child

private theorem expectedEightElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 8 .lambdaOrdinary)
      (expectedCore .lambdaOrdinary) .word :=
  expectedGenericElaborates file 8 .lambdaOrdinary (by decide)

private theorem expectedNineElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 9 .ordinaryLambda)
      (expectedCore .ordinaryLambda) .word :=
  expectedGenericElaborates file 9 .ordinaryLambda (by decide)

private theorem expectedSixteenElaborates (file : Syntax.SourceFile) :
    LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
      types owner inputs (expectedSource file 16 .lambdaLambda)
      (expectedCore .lambdaLambda) .word :=
  expectedGenericElaborates file 16 .lambdaLambda (by decide)

private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value :=
  .closure .unit .word (.var 99)
    [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value :=
  .closure functionType .word (.apply (.var 0) (.word seven))
    [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value :=
  .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment :=
  [applyValue, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store :=
  [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]

private def runGenerated
    (runtimeLabel : String) (candidate : Core.Expr) (choice : Bool) : IO Unit := do
  match Core.runStateful 13 (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError s!"{runtimeLabel}: completed with fuel 13")
  match Core.runStateful 14 (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
      check (value == .word seven && finalStore == store)
        s!"{runtimeLabel}: wrong result or mutated store"
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out of fuel at 14")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: Core fault")

private def verifySuccess (depth : Nat) (mode : Mode)
    (staticRelation : ∀ file : Syntax.SourceFile,
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs (expectedSource file depth mode) (expectedCore mode) .word) :
    IO Unit := do
  let (file, parsed) ← parseComplete s!"generic-{depth}-{label mode}.sol"
    (groupedCallText depth (conditionalText mode))
  let some equality := exactExpectedSource? file depth mode parsed |
    throw (IO.userError s!"depth {depth}: exact AST/span equality")
  proof equality.down
  have parsedRelation :
      LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
        types owner inputs parsed (expectedCore mode) .word := by
    rw [equality.down]
    exact staticRelation file
  proof parsedRelation
  proof parsedRelation.core_hasType
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let expected := some (expectedCore mode, .word)
  check (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == expected && wrapped == expected)
    s!"depth {depth}: generic elaboration changed"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    proof
      (elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
        (types := types) (owner := owner) (inputs := inputs) boundary)
  else
    throw (IO.userError s!"depth {depth}: classifier proof")
  match wrapped with
  | some (candidate, .word) =>
      if accepted : wrapped = some (candidate, .word) then
        let relation :=
          elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_iff.mp accepted
        proof relation
        proof relation.core_hasType
      else
        throw (IO.userError s!"depth {depth}: correspondence proof")
      for choice in [false, true] do
        runGenerated s!"depth {depth}/{label mode}/{choice}" candidate choice
  | _ => throw (IO.userError s!"depth {depth}: missing generated word Core")

private def verifySevenLevelPreservation : IO Unit := do
  let (_, parsed) ← parseComplete "generic-false-side-depth-7.sol"
    (groupedCallText 7 (conditionalText .lambdaOrdinary))
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let previous :=
    elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  let expected := some (expectedCore .lambdaOrdinary, .word)
  check (!isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child.isNone && previous == expected && wrapped == previous)
    "depth 7: predecessor result was not preserved"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    let route :=
      elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_existing
        (types := types) (owner := owner) (inputs := inputs) boundary
    proof route
    if accepted : previous = some (expectedCore .lambdaOrdinary, .word) then
      let predecessor :=
        elaborateLocalApplicationWithSevenLevelGroupedConditionalExpectedLambda?_iff.mp accepted
      let relation : LocalApplicationWithGenericGroupedConditionalExpectedLambdaElaborates
          types owner inputs parsed (expectedCore .lambdaOrdinary) .word :=
        .existing boundary predecessor
      proof relation
      proof relation.core_hasType
    else
      throw (IO.userError "depth 7: predecessor correspondence proof")
  else
    throw (IO.userError "depth 7: false-side classifier proof")

private def verifySelectedFailureIsFinal : IO Unit := do
  let (_, parsed) ← parseComplete "generic-selected-failure.sol"
    (groupedCallText 8 "wrong ? lam(x){return x;} : ordinary")
  let child :=
    elaborateEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed
  let wrapped :=
    elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?
      types owner inputs parsed
  check (isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child.isNone && wrapped == child && wrapped.isNone)
    "selected semantic failure was not final"
  if boundary :
      isEightOrMoreGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if rejected : child = none then
      let route :=
        elaborateLocalApplicationWithGenericGroupedConditionalExpectedLambda?_of_eightOrMoreGroupedConditional
          (types := types) (owner := owner) (inputs := inputs) boundary
      proof route
      proof (show wrapped = none by simpa only [wrapped, child] using route.trans rejected)
    else
      throw (IO.userError "selected failure: child rejection proof")
  else
    throw (IO.userError "selected failure: classifier proof")

private def exercise : IO Unit := do
  verifySuccess 8 .lambdaOrdinary expectedEightElaborates
  verifySuccess 9 .ordinaryLambda expectedNineElaborates
  verifySuccess 16 .lambdaLambda expectedSixteenElaborates
  verifySevenLevelPreservation
  verifySelectedFailureIsFinal

end Tests.FrontendParsedGenericGroupedConditional

def Tests.genericGroupedConditionalTests : IO Unit :=
  FrontendParsedGenericGroupedConditional.exercise *>
    IO.println "parsed generic grouped conditional adapter GREEN"
