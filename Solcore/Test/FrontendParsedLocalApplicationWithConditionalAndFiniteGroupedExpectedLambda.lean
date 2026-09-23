import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
/-! Independent parsed integration consumer for conditional-first finite-group dispatch. -/
set_option autoImplicit false
namespace Tests.ADR0325ParsedUnifiedConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda | allOrdinary | grouped
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnifiedExpectedLambda", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 325
private def foreignOwner := declaration 9325
private def localId (owner : Resolved.DeclarationId) (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5),
      .inferred ⟨range file (start + 4) (start + 5), "x"⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16),
      .returnStmt (some (reference file (start + 14) (start + 15) "x"))⟩]⟩⟩
private def conditionalSource (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 0 42, .call (reference file 0 5 "apply") ⟨range file 5 42,
    [⟨range file 6 41, .conditional (reference file 6 10 "flag") (range file 11 12)
      (lambdaAt file 13) (range file 31 32) (reference file 33 41 "ordinary")⟩]⟩⟩
private def twoGrouped (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 6 27, .group ⟨range file 7 26, .group (lambdaAt file 8)⟩⟩
private def twoSource (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 0 28, .call (reference file 0 5 "apply") ⟨range file 5 28, [twoGrouped file]⟩⟩
private def threeGrouped (file : Syntax.SourceFile) : Syntax.Expr :=
  ⟨range file 6 29, .group ⟨range file 7 28, .group
    ⟨range file 8 27, .group (lambdaAt file 9)⟩⟩⟩
private def threeSource (file : Syntax.SourceFile) : Syntax.Expr := ⟨range file 0 30, .call (reference file 0 5 "apply") ⟨range file 5 30, [threeGrouped file]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def groupedCore : Core.Expr := .apply (.var 0) lambdaCore
private def conditionalCore : Core.Expr := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
private theorem calleeElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates
    inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagElaboration (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 6 10 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryElaboration (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaElaboration (file : Syntax.SourceFile) (start : Nat) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda
    (header := ⟨inputs.bindFresh owner "x" .word, ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) "x"))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda
      ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression
      (.pure (.identifier .head) (.var .head) (.var .head))
private theorem conditionalChild (file : Syntax.SourceFile) : ConditionalExpectedLambdaArgumentApplicationElaborates
    types owner inputs (conditionalSource file) conditionalCore .word :=
  .application rfl (calleeElaboration file) (flagElaboration file)
    (.expected rfl (lambdaElaboration file 13)) (.ordinary rfl (ordinaryElaboration file 33 41))
private theorem threeChild (file : Syntax.SourceFile) : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
    types owner inputs (threeSource file) groupedCore .word :=
  .application (.group (.group (.group .lambda)))
    (calleeElaboration file) (lambdaElaboration file 9)
private theorem twoChild (file : Syntax.SourceFile) : LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates
    types owner inputs (twoSource file) groupedCore .word :=
  .twoLevel rfl (.application (calleeElaboration file) (lambdaElaboration file 8))
private theorem nonGroupBoundaries (file : Syntax.SourceFile) : isThreeOrMoreGroupedExpectedLambdaArgumentApplication (conditionalSource file) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (twoSource file) = false := by
  constructor <;> cases selected : isThreeOrMoreGroupedExpectedLambdaArgumentApplication _
  · rfl
  · rcases isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected with ⟨_, _, _, _, _, spine⟩
    cases spine
  · rfl
  · rcases isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected with ⟨_, _, _, _, _, spine⟩
    cases spine with | group child => cases child with | group child => cases child
private theorem conditionalWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (conditionalSource file) conditionalCore .word :=
  .conditional rfl (conditionalChild file)
private theorem threeWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (threeSource file) groupedCore .word :=
  .threeOrMoreGrouped rfl (threeChild file).classified (threeChild file)
private theorem twoWrapper (file : Syntax.SourceFile) : LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word :=
  .existing rfl (nonGroupBoundaries file).2 (twoChild file)
/-! The exact routes retain child, wrapper, executable, classifier, typing and provenance. -/
theorem parsed_unified_static_contract (file : Syntax.SourceFile) :
    (ConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (conditionalSource file) conditionalCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (conditionalSource file) conditionalCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (conditionalSource file) = some (conditionalCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (conditionalSource file) = true ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (conditionalSource file) = false ∧
      Core.HasType inputs.context.values conditionalCore .word) ∧
    (ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs (threeSource file) groupedCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (threeSource file) groupedCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (threeSource file) = some (groupedCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (threeSource file) = false ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (threeSource file) = true ∧
      Core.HasType inputs.context.values groupedCore .word) ∧
    (LocalApplicationWithTwoLevelGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word ∧
      LocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaElaborates types owner inputs (twoSource file) groupedCore .word ∧
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs
        (twoSource file) = some (groupedCore, .word) ∧
      isConditionalExpectedLambdaArgumentApplication (twoSource file) = false ∧
      isThreeOrMoreGroupedExpectedLambdaArgumentApplication (twoSource file) = false ∧
      Core.HasType inputs.context.values groupedCore .word) := by
  have c := conditionalWrapper file
  have g := threeWrapper file
  have e := twoWrapper file
  exact ⟨⟨conditionalChild file, c,
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr c,
      rfl, (nonGroupBoundaries file).1, c.core_hasType⟩,
    ⟨threeChild file, g, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr g,
      rfl, (threeChild file).classified, g.core_hasType⟩,
    ⟨twoChild file, e, elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_iff.mpr e,
      rfl, (nonGroupBoundaries file).2, e.core_hasType⟩⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99)
  [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word
  (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : List Core.Value :=
  [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
private def runtimeCore : Mode → Core.Expr
  | .lambdaOrdinary => conditionalCore
  | .ordinaryLambda => .apply (.var 0) (.ifE (.var 3) (.var 4) lambdaCore)
  | .lambdaLambda => .apply (.var 0) (.ifE (.var 3) lambdaCore lambdaCore)
  | .allOrdinary => .apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4))
  | .grouped => groupedCore
/-! Every selected Core shape has an independent big-step derivation. -/
theorem independently_executed_unified_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (runtimeCore mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"
    pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, "x"⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, "x"⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start + 17) ∧ ks = range file start (start + 3) ∧
        ps = range file (start + 3) (start + 6) ∧ p = range file (start + 4) (start + 5) ∧
        pn = range file (start + 4) (start + 5) ∧ bs = range file (start + 6) (start + 17) ∧
        ss = range file (start + 7) (start + 16) ∧ rs = range file (start + 14) (start + 15) ∧
        rn = range file (start + 14) (start + 15) then some ⟨by
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl⟩ else none
  | _ => none
private def exactConditional? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = conditionalSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as, [⟨is, .conditional
      ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon ⟨os, .identifier ⟨ons, "ordinary"⟩⟩⟩]⟩⟩ => do
    let yesEq ← exactLambda? file 13 yes
    if h : cs = range file 0 42 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 42 ∧ is = range file 6 41 ∧ fs = range file 6 10 ∧
        fns = range file 6 10 ∧ q = range file 11 12 ∧ colon = range file 31 32 ∧
        os = range file 33 41 ∧ ons = range file 33 41 then some ⟨by
      rw [yesEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩
    else none
  | _ => none
private def exactTwo? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = twoSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨o, .group ⟨i, .group terminal⟩⟩]⟩⟩ => do
    let terminalEq ← exactLambda? file 8 terminal
    if h : cs = range file 0 28 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 28 ∧ o = range file 6 27 ∧ i = range file 7 26 then some ⟨by
      rw [terminalEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactThree? (file : Syntax.SourceFile) (candidate : Syntax.Expr) : Option (PLift (candidate = threeSource file)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨o, .group ⟨m, .group ⟨i, .group terminal⟩⟩⟩]⟩⟩ => do
    let terminalEq ← exactLambda? file 9 terminal
    if h : cs = range file 0 30 ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 30 ∧ o = range file 6 29 ∧ m = range file 7 28 ∧
        i = range file 8 27 then some ⟨by
      rw [terminalEq.down]; rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def accepted (label text : String) (conditional grouped : Bool) (expected : Core.Expr) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == conditional &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped &&
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed == some (expected, .word)) s!"{label}: route or endpoint changed"
private def verifyExactParses : IO Unit := do
  let (cf, cp) ← parseComplete "adr0325-conditional-exact.sol"
    "apply(flag ? lam(x){return x;} : ordinary)"
  let some ce := exactConditional? cf cp | throw (IO.userError "conditional: exact AST/spans differ")
  proof (ce.down ▸ And.intro (parsed_unified_static_contract cf).1 (conditionalWrapper cf).provenance)
  let (gf, gp) ← parseComplete "adr0325-three-exact.sol" "apply((((lam(x){return x;}))))"
  let some ge := exactThree? gf gp | throw (IO.userError "depth3: exact AST/spans differ")
  proof (ge.down ▸ And.intro (parsed_unified_static_contract gf).2.1 (threeWrapper gf).provenance)
  let (ef, ep) ← parseComplete "adr0325-two-exact.sol" "apply(((lam(x){return x;})))"
  let some ee := exactTwo? ef ep | throw (IO.userError "depth2: exact AST/spans differ")
  proof (ee.down ▸ And.intro (parsed_unified_static_contract ef).2.2 (twoWrapper ef).provenance)
private def runExact (label : String) (low high : Nat) (choice : Bool) (mode : Mode)
    (expected : Core.Evaluates (environment choice) store (runtimeCore mode) (.word seven) store) : IO Unit := do
  match Core.runStateful low (Core.State.initial (runtimeCore mode) (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{label}: completed below exact fuel")
  match actualRun : Core.runStateful high (Core.State.initial (runtimeCore mode) (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{label}: result or store changed"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actualRun) expected)
  | .outOfFuel _ => throw (IO.userError s!"{label}: no result at exact fuel")
  | .fault _ _ => throw (IO.userError s!"{label}: Core faulted")
private def verifyRuntime : IO Unit := do
  for (label, text, mode) in [
      ("lambda-ordinary", "apply(flag ? lam(x){return x;} : ordinary)", Mode.lambdaOrdinary),
      ("ordinary-lambda", "apply(flag ? ordinary : lam(x){return x;})", .ordinaryLambda),
      ("lambda-lambda", "apply(flag ? lam(x){return x;} : lam(y){return y;})", .lambdaLambda)] do
    accepted label text true false (runtimeCore mode)
    for choice in [false, true] do
      runExact s!"{label}-{choice}" 13 14 choice mode (by
        simpa [environment] using independently_executed_unified_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
  accepted "all-ordinary" "apply(flag ? ordinary : ordinary)" false false (runtimeCore .allOrdinary)
  for choice in [false, true] do
    runExact s!"all-ordinary-{choice}" 13 14 choice .allOrdinary (by
      simpa [environment] using independently_executed_unified_core .allOrdinary choice
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
  for (label, text, grouped) in [("depth2", "apply(((lam(x){return x;})))", false),
      ("depth3", "apply((((lam(x){return x;}))))", true),
      ("depth4", "apply(((((lam(x){return x;})))))", true),
      ("depth8", "apply(((((((((lam(x){return x;})))))))))", true)] do
    accepted label text false grouped groupedCore
    runExact label 10 11 false .grouped (by
      simpa [environment] using independently_executed_unified_core .grouped false
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store)
private def rejected (label text : String) (conditional grouped : Bool) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
  check (isConditionalExpectedLambdaArgumentApplication parsed == conditional &&
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped &&
    (elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed).isNone) s!"{label}: recognized failure changed"
private def verifyBoundaries : IO Unit := do
  for (label, text) in [
      ("condition-type", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("bad-header", "apply(flag ? lam(x,y){return x;} : ordinary)"),
      ("other-type", "apply(flag ? lam(x){return x;} : wrong)"),
      ("callee-missing", "missing(flag ? lam(x){return x;} : ordinary)"),
      ("mixed-grouped", "apply(flag ? lam(x){return x;} : (lam(y){return y;}))")] do
    rejected label text true false
  for (label, text) in [("group-header", "apply((((lam(x,y){return x;}))))"),
      ("group-body", "apply((((lam(x){return flag;}))))"),
      ("group-nonfunction", "flag((((lam(x){return x;}))))"),
      ("group-missing", "missing((((lam(x){return x;}))))")] do
    rejected label text false true
  for (label, text) in [
      ("grouped-conditional", "apply((flag ? lam(x){return x;} : ordinary))"),
      ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("zero", "apply()"),
      ("multi", "apply(lam(x){return x;},ordinary)"),
      ("top", "flag ? lam(x){return x;} : ordinary")] do
    let (_, parsed) ← parseComplete s!"adr0325-{label}.sol" text
    check (!isConditionalExpectedLambdaArgumentApplication parsed &&
      !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
      elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
        types owner inputs parsed == elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda?
          types owner inputs parsed) s!"{label}: frozen ADR0322 equality changed"
  for (label, text, expected) in [("direct", "apply(lam(x){return x;})", groupedCore),
      ("one-group", "apply((lam(x){return x;}))", groupedCore),
      ("ordinary0", "apply(ordinary)", .apply (.var 0) (.var 4)),
      ("ordinary1", "apply((ordinary))", .apply (.var 0) (.var 4)),
      ("ordinary3", "apply((((ordinary))))", .apply (.var 0) (.var 4))] do
    accepted label text false false expected
private def exercise : IO Unit := do verifyExactParses; verifyRuntime; verifyBoundaries
end Tests.ADR0325ParsedUnifiedConsumerIndependent
/-! Run all parsed ADR-0325 integration checks. -/
def Tests.adr0325ParsedLocalApplicationWithConditionalAndFiniteGroupedExpectedLambdaTests : IO Unit := do
  ADR0325ParsedUnifiedConsumerIndependent.exercise
  IO.println "ADR0325 parsed conditional-first finite-group consumer GREEN"
