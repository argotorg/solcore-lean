import Solcore.Frontend.OneLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
/-! Independent parsed consumer for one grouped conditional application argument. -/
set_option autoImplicit false
namespace Tests.ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 326
private def foreignOwner := declaration 9326
private def localId (o : Resolved.DeclarationId) (n : Nat) : Resolved.LocalId := ⟨o, n⟩
private def functionType : Core.Ty := .function .word .word
private def inputs : LocalTypeInputs := ⟨[⟨"apply", localId owner 17, .function functionType .word⟩,
  ⟨"opaque", localId foreignOwner 700, .cell (.function .word .unit)⟩, ⟨"apply", localId owner 3, .unit⟩,
  ⟨"flag", localId foreignOwner 701, .bool⟩, ⟨"ordinary", localId owner 29, functionType⟩,
  ⟨"wrong", localId foreignOwner 702, .word⟩], by decide⟩
private def types : TypeNameTable := []
private def range (file : Syntax.SourceFile) (start stop : Nat) : Syntax.SourceSpan := ⟨file.id, start, stop⟩
private def reference (file : Syntax.SourceFile) (start stop : Nat) (name : String) : Syntax.Expr := ⟨range file start stop, .identifier ⟨range file start stop, name⟩⟩
private def lambdaAt (file : Syntax.SourceFile) (start : Nat) (name : String) : Syntax.Expr :=
  ⟨range file start (start + 17), .lambda (range file start (start + 3))
    ⟨range file (start + 3) (start + 6), [⟨range file (start + 4) (start + 5), .inferred ⟨range file (start + 4) (start + 5), name⟩⟩]⟩ none
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 14 "x"
  | .ordinaryLambda => reference file 14 22 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 34 42 "ordinary"
  | .ordinaryLambda => lambdaAt file 25 "x"
  | .lambdaLambda => lambdaAt file 34 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 32 33
  | .ordinaryLambda => range file 23 24
private def conditionalStop : Mode → Nat | .lambdaLambda => 51 | _ => 42
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 2), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 2),
    [⟨range file 6 (stop + 1), .group ⟨range file 7 stop, .conditional
      (reference file 7 11 "flag") (range file 12 13) (thenSource file mode)
      (colonRange file mode) (elseSource file mode)⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 7 11 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start + 6) (start + 17), [⟨range file (start + 7) (start + 16), .returnStmt (some (reference file (start + 14) (start + 15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .expected rfl (lambdaE file 14 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 14 22)
  | lambdaLambda => exact .expected rfl (lambdaE file 14 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 34 42)
  | ordinaryLambda => exact .expected rfl (lambdaE file 25 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 34 "y")
private theorem sourceE (file : Syntax.SourceFile) (mode : Mode) : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  constructor
  · rfl
  · apply Bool.eq_false_iff.mpr; intro selected
    obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
    cases spine with | group child => cases child
/-- Parsed sources retain the complete new relation, endpoint, partition and provenance. -/
theorem parsed_one_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs (source file mode) =
      elaborateLocalApplicationWithTwoLevelGroupedExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have e := sourceE file mode; have old := oldBoundaries file mode
  exact ⟨e, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr e,
    e.classified, old.1, old.2,
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?_of_existing old.1 old.2,
    e.core_hasType⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Both choices execute every grouped-conditional Core without changing the store. -/
theorem independently_executed_one_group_conditional_core (mode : Mode) (choice : Bool)
    (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow]
      initialStore (core mode) (.word seven) initialStore := by
  cases mode <;> cases choice
  · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String
  | .lambdaOrdinary => "apply((flag ? lam(x){return x;} : ordinary))"
  | .ordinaryLambda => "apply((flag ? ordinary : lam(x){return x;}))"
  | .lambdaLambda => "apply((flag ? lam(x){return x;} : lam(y){return y;}))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer rejected")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next =>
    check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file)
      s!"{path}: parser diagnostics, EOF or full span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser rejected")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with
  | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ =>
    if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name
      then some ⟨by rcases h with ⟨rfl, rfl, rfl⟩; rfl⟩ else none
  | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String)
    (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none
      ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧
        ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧
        pn = range file (start+4) (start+5) ∧ observed = name ∧
        bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧
        rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨gs, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+2) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧
        as = range file 5 (conditionalStop mode+2) ∧ gs = range file 6 (conditionalStop mode+1) ∧
        is = range file 7 (conditionalStop mode) ∧ fs = range file 7 11 ∧ fns = range file 7 11 ∧
        q = range file 12 13 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 14 "x" yes; let n ← exactReference? file 34 42 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 14 22 "ordinary" yes; let n ← exactLambda? file 25 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 14 "x" yes; let n ← exactLambda? file 34 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0326-{label mode}.sol" (modeText mode)
  let some eq := exactSource? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed == some (core mode, .word)) s!"{label mode}: static endpoint"
  proof (eq.down ▸ parsed_one_group_conditional_static_contract file mode)
  proof (sourceE file mode).provenance
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0326-{label}.sol" text
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    !isConditionalExpectedLambdaArgumentApplication parsed &&
    !isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed &&
    (elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone) s!"{label}: recognized failure changed"
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((wrong ? lam(x){return x;} : ordinary))"),
      ("condition-missing", "apply((missing ? lam(x){return x;} : ordinary))"),
      ("header", "apply((flag ? lam(x,y){return x;} : ordinary))"),
      ("body", "apply((flag ? lam(x){return flag;} : ordinary))"),
      ("other-type", "apply((flag ? lam(x){return x;} : wrong))"),
      ("other-missing", "apply((flag ? lam(x){return x;} : missing))"),
      ("nonfunction", "flag((flag ? lam(x){return x;} : ordinary))"),
      ("mixed-grouped", "apply((flag ? lam(x){return x;} : (lam(y){return y;})))"),
      ("mixed-nested", "apply((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))"),
      ("callee-missing", "globalApply((flag ? lam(x){return x;} : ordinary))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty)) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0326-{label}.sol" text
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    (elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?
      types owner inputs parsed).isNone &&
    elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda?
      types owner inputs parsed == expected) s!"{label}: frozen neighbor changed"
private def verifyPreservation : IO Unit := do
  preserved "ungrouped" "apply(flag ? lam(x){return x;} : ordinary)"
    (some (.apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4)), .word))
  preserved "all-ordinary" "apply((flag ? ordinary : ordinary))"
    (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word))
  preserved "branch-grouped" "apply(flag ? (lam(x){return x;}) : ordinary)" none
  preserved "two-outer" "apply(((flag ? lam(x){return x;} : ordinary)))" none
  preserved "one-lambda-group" "apply((lam(x){return x;}))" (some (.apply (.var 0) lambdaCore, .word))
  preserved "three-lambda-groups" "apply((((lam(x){return x;}))))" (some (.apply (.var 0) lambdaCore, .word))
  preserved "direct-lambda" "apply(lam(x){return x;})" (some (.apply (.var 0) lambdaCore, .word))
  preserved "ordinary" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word))
  preserved "ordinary-depth3" "apply((((ordinary))))" (some (.apply (.var 0) (.var 4), .word))
  for (label, text) in [("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"),
      ("top", "(flag ? lam(x){return x;} : ordinary)"),
      ("tuple", "apply((lam(x){return x;},ordinary))"),
      ("nested-call", "apply(ordinary(lam(x){return x;}))")] do preserved label text none
private def runExact (mode : Mode) (choice : Bool) : IO Unit := do
  match Core.runStateful 13 (Core.State.initial (core mode) (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{label mode}: completed below 14")
  match actual : Core.runStateful 14 (Core.State.initial (core mode) (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{label mode}: result/store"
    have expected : Core.Evaluates (environment choice) store (core mode) (.word seven) store := by
      simpa [environment] using independently_executed_one_group_conditional_core mode choice
        opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{label mode}: out at 14")
  | .fault _ _ => throw (IO.userError s!"{label mode}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode
    for choice in [false, true] do runExact mode choice
  verifyFailures
  verifyPreservation
end Tests.ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent
/-- Run all parsed ADR-0326 grouped-conditional checks. -/
def Tests.adr0326ParsedOneLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0326ParsedOneLevelGroupedConditionalConsumerIndependent.exercise
  IO.println "ADR0326 parsed one-level grouped conditional consumer GREEN"
