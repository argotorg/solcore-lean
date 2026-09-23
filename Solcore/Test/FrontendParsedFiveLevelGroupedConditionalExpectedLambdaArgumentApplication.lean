import Solcore.Frontend.FiveLevelGroupedConditionalExpectedLambdaArgumentApplication
import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
namespace Tests.ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedFiveGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 334
private def foreignOwner := declaration 9334
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
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 18 "x"
  | .ordinaryLambda => reference file 18 26 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 38 46 "ordinary"
  | .ordinaryLambda => lambdaAt file 29 "x"
  | .lambdaLambda => lambdaAt file 38 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 36 37
  | .ordinaryLambda => range file 27 28
private def conditionalStop : Mode → Nat | .lambdaLambda => 55 | _ => 46
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 6), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 6),
    [⟨range file 6 (stop + 5), .group ⟨range file 7 (stop + 4), .group
      ⟨range file 8 (stop + 3), .group ⟨range file 9 (stop + 2), .group
        ⟨range file 10 (stop + 1), .group ⟨range file 11 stop, .conditional
          (reference file 11 15 "flag") (range file 16 17)
          (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 11 15 "flag") (.var 3) .bool :=
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
  | lambdaOrdinary => exact .expected rfl (lambdaE file 18 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 18 26)
  | lambdaLambda => exact .expected rfl (lambdaE file 18 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 38 46)
  | ordinaryLambda => exact .expected rfl (lambdaE file 29 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 38 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_five_group_conditional_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    FiveLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    isFourLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧
    Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; rcases oldBoundaries file mode with ⟨four, three, two, one, immediate, generic⟩
  have route := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_of_existing (types := types) (owner := owner) (inputs := inputs) four
  exact ⟨child, child.classified, four, three, two, one, immediate, generic,
    elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    route, child.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    (if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication s then elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? t o i s else elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s) =
      elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? t o i s := by
  simp [boundary]
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_five_group_conditional_core (mode : Mode) (choice : Bool)
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
private def modeText : Mode → String | .lambdaOrdinary => "apply((((((flag ? lam(x){return x;} : ordinary))))))" | .ordinaryLambda => "apply((((((flag ? ordinary : lam(x){return x;}))))))" | .lambdaLambda => "apply((((((flag ? lam(x){return x;} : lam(y){return y;}))))))"
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
    if h : ls = range file start (start+17) ∧ ks = range file start (start+3) ∧ ps = range file (start+3) (start+6) ∧ p = range file (start+4) (start+5) ∧ pn = range file (start+4) (start+5) ∧ observed = name ∧ bs = range file (start+6) (start+17) ∧ ss = range file (start+7) (start+16) ∧ rs = range file (start+14) (start+15) ∧ rn = range file (start+14) (start+15) ∧ result = name
      then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSuccess? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨deepest, .group
        ⟨innermost, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+6) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+6) ∧ outer = range file 6 (conditionalStop mode+5) ∧ middle = range file 7 (conditionalStop mode+4) ∧ inner = range file 8 (conditionalStop mode+3) ∧ deepest = range file 9 (conditionalStop mode+2) ∧ innermost = range file 10 (conditionalStop mode+1) ∧ is = range file 11 (conditionalStop mode) ∧ fs = range file 11 15 ∧ fns = range file 11 15 ∧ q = range file 16 17 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 18 "x" yes; let n ← exactReference? file 38 46 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 18 26 "ordinary" yes; let n ← exactLambda? file 29 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 18 "x" yes; let n ← exactLambda? file 38 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional4 | conditional6 | lambda5
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional4 => callAt file 50 ⟨range file 6 49, .group ⟨range file 7 48, .group ⟨range file 8 47, .group ⟨range file 9 46, .group (conditionalAt file 10)⟩⟩⟩⟩
  | .conditional6 => callAt file 54 ⟨range file 6 53, .group ⟨range file 7 52, .group ⟨range file 8 51, .group ⟨range file 9 50, .group ⟨range file 10 49, .group ⟨range file 11 48, .group (conditionalAt file 12)⟩⟩⟩⟩⟩⟩
  | .lambda5 => callAt file 34 ⟨range file 6 33, .group ⟨range file 7 32, .group ⟨range file 8 31, .group ⟨range file 9 30, .group ⟨range file 10 29, .group (lambdaAt file 11 "x")⟩⟩⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional4, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 10 14 "flag" condition; let y ← exactLambda? file 17 "x" yes; let n ← exactReference? file 37 45 "ordinary" no
    if h : cs=range file 0 50 ∧ as=range file 5 50 ∧ a=range file 6 49 ∧ b=range file 7 48 ∧ c=range file 8 47 ∧ d=range file 9 46 ∧ is=range file 10 45 ∧ q=range file 15 16 ∧ colon=range file 35 36 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional6, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group ⟨f, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let flag ← exactReference? file 12 16 "flag" condition; let y ← exactLambda? file 19 "x" yes; let n ← exactReference? file 39 47 "ordinary" no
    if h : cs=range file 0 54 ∧ as=range file 5 54 ∧ a=range file 6 53 ∧ b=range file 7 52 ∧ c=range file 8 51 ∧ d=range file 9 50 ∧ e=range file 10 49 ∧ f=range file 11 48 ∧ is=range file 12 47 ∧ q=range file 17 18 ∧ colon=range file 37 38 then some ⟨by rw [ca.down,flag.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda5, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨e, .group body⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let bodyEq ← exactLambda? file 11 "x" body
    if h : cs=range file 0 34 ∧ as=range file 5 34 ∧ a=range file 6 33 ∧ b=range file 7 32 ∧ c=range file 8 31 ∧ d=range file 9 30 ∧ e=range file 10 29 then some ⟨by rw [ca.down,bodyEq.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0334-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && planned == child) s!"{label mode}: exact planned route"
  proof (equality.down ▸ parsed_five_group_conditional_static_contract file mode)
  proof (childE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0334-{label}.sol" text
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == child && planned.isNone) s!"{label}: selected failure changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      proof (show planned = none by simp only [planned, boundary, childNone, ↓reduceIte])
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((((((wrong ? lam(x){return x;} : ordinary))))))"),
      ("condition-missing", "apply((((((missing ? lam(x){return x;} : ordinary))))))"),
      ("header", "apply((((((flag ? lam(x,y){return x;} : ordinary))))))"),
      ("body", "apply((((((flag ? lam(x){return flag;} : ordinary))))))"),
      ("other-type", "apply((((((flag ? lam(x){return x;} : wrong))))))"),
      ("other-missing", "apply((((((flag ? lam(x){return x;} : missing))))))"),
      ("nonfunction", "flag((((((flag ? lam(x){return x;} : ordinary))))))"),
      ("callee-missing", "globalApply((((((flag ? lam(x){return x;} : ordinary))))))"),
      ("mixed-grouped", "apply((((((flag ? lam(x){return x;} : (lam(y){return y;})))))))"),
      ("mixed-nested", "apply((((((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0334-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateFiveLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let planned := if isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed then child else previous
  check (!isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    planned == previous && previous == expected) s!"{label}: complete ADR0333 Option changed"
  if boundary : isFiveLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof (show planned = expected by simpa only [planned, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithFourLevelGroupedConditionalExpectedLambda?_iff.mp accepted; proof relation; proof relation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0333 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) none
  preserved "three-group-conditional" "apply((((flag ? lam(x){return x;} : ordinary))))" (some (conditionalCore, .word)) none
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" (some (conditionalCore, .word)) (some .conditional4)
  preserved "six-group-conditional" "apply(((((((flag ? lam(x){return x;} : ordinary)))))))" none (some .conditional6)
  preserved "all-ordinary" "apply((((((flag ? ordinary : ordinary))))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))"),
      (5, "five-lambda-groups", "apply((((((lam(x){return x;}))))))"),
      (6, "six-lambda-groups", "apply(((((((lam(x){return x;})))))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 5 then some .lambda5 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply((((((flag ? (lam(x){return x;}) : ordinary))))))"),
      ("nested-only", "apply((((((flag ? ordinary(lam(x){return x;}) : ordinary))))))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
      ("adr0332-failure", "apply(((((wrong ? lam(x){return x;} : ordinary)))))"), ("adr0330-failure", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("adr0328-failure", "apply(((wrong ? lam(x){return x;} : ordinary)))"),
      ("adr0326-failure", "apply((wrong ? lam(x){return x;} : ordinary))"), ("adr0324-failure", "apply(wrong ? lam(x){return x;} : ordinary)"),
      ("adr0323-failure", "apply((((lam(x,y){return x;}))))"), ("adr0322-failure", "apply(((lam(x,y){return x;})))"), ("adr0320-failure", "apply((lam(x,y){return x;}))"), ("adr0317-failure", "apply(lam(x,y){return x;})"),
      ("zero", "apply()"), ("multi", "apply(lam(x){return x;},ordinary)"), ("top", "((flag ? lam(x){return x;} : ordinary))")] do preserved label text none none
private def directCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem directE (choice : Bool) : Core.Evaluates (environment choice) store directCore (.word seven) store :=
  .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def runExact (runtimeLabel : String) (below complete : Nat) (candidate : Core.Expr) (choice : Bool)
    (expected : Core.Evaluates (environment choice) store candidate (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial candidate (environment choice) store) with
  | .outOfFuel _ => pure () | _ => throw (IO.userError s!"{runtimeLabel}: completed below {complete}")
  match actual : Core.runStateful complete (Core.State.initial candidate (environment choice) store) with
  | .done value finalStore =>
    check (value == .word seven && finalStore == store) s!"{runtimeLabel}: result/store"
    proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError s!"{runtimeLabel}: out at {complete}")
  | .fault _ _ => throw (IO.userError s!"{runtimeLabel}: fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary, .ordinaryLambda, .lambdaLambda] do
    verifySuccess mode; for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_five_group_conditional_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_five_group_conditional_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    for runtimeLabel in ["immediate-conditional", "one-group-conditional", "two-group-conditional", "three-group-conditional", "four-group-conditional"] do
      runExact runtimeLabel 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    for runtimeLabel in ["direct-lambda", "one-lambda-group", "two-lambda-groups", "three-lambda-groups", "four-lambda-groups", "five-lambda-groups", "six-lambda-groups"] do
      runExact runtimeLabel 10 11 directCore choice (directE choice)
  verifyFailures; verifyPreservation
end Tests.ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent
def Tests.adr0334ParsedFiveLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0334ParsedFiveLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0334 parsed five-level grouped conditional adapter GREEN"
