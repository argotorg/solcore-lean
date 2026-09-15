import Solcore.Frontend.LocalApplicationWithThreeLevelGroupedConditionalExpectedLambda
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
namespace Tests.ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedThreeGroupedWrapper", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 331
private def foreignOwner := declaration 9331
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
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 16 "x"
  | .ordinaryLambda => reference file 16 24 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 36 44 "ordinary"
  | .ordinaryLambda => lambdaAt file 27 "x"
  | .lambdaLambda => lambdaAt file 36 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 34 35
  | .ordinaryLambda => range file 25 26
private def conditionalStop : Mode → Nat | .lambdaLambda => 53 | _ => 44
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop + 4), .call (reference file 0 5 "apply") ⟨range file 5 (stop + 4),
    [⟨range file 6 (stop + 3), .group ⟨range file 7 (stop + 2), .group
      ⟨range file 8 (stop + 1), .group ⟨range file 9 stop, .conditional
        (reference file 9 13 "flag") (range file 14 15) (thenSource file mode)
        (colonRange file mode) (elseSource file mode)⟩⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def core (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 9 13 "flag") (.var 3) .bool :=
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
  | lambdaOrdinary => exact .expected rfl (lambdaE file 16 "x")
  | ordinaryLambda => exact .ordinary rfl (ordinaryE file 16 24)
  | lambdaLambda => exact .expected rfl (lambdaE file 16 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with
  | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 36 44)
  | ordinaryLambda => exact .expected rfl (lambdaE file 27 "x")
  | lambdaLambda => exact .expected rfl (lambdaE file 36 "y")
private theorem childE (file : Syntax.SourceFile) (mode : Mode) : ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word := .threeLevelGroupedConditional (childE file mode).classified (childE file mode)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) :
    isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  apply Bool.eq_false_iff.mpr; intro selected
  obtain ⟨_, _, _, _, _, spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
  cases spine with | group child => cases child with | group child => cases child with | group child => cases child
theorem parsed_three_group_wrapper_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    ThreeLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (core mode) .word ∧ LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (core mode) .word ∧
    isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧ isTwoLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧ elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (core mode, .word) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) ∧
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (core mode, .word) ∧ elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) ∧ Core.HasType inputs.context.values (core mode) .word := by
  have child := childE file mode; have wrapped := wrapperE file mode; have old := oldBoundaries file mode
  exact ⟨child, wrapped, child.classified, old.1, old.2.1, old.2.2.1, old.2.2.2,
    elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional child.classified,
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_of_existing old.1, wrapped.core_hasType⟩
private theorem falseRoute {t : TypeNameTable} {o : Resolved.DeclarationId} {i : LocalTypeInputs} {s : Syntax.Expr}
    (boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication s = false) :
    elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? t o i s = elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? t o i s :=
  elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_existing boundary
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
theorem independently_executed_three_group_wrapper_core (mode : Mode) (choice : Bool)
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
  | .lambdaOrdinary => "apply((((flag ? lam(x){return x;} : ordinary))))"
  | .ordinaryLambda => "apply((((flag ? ordinary : lam(x){return x;}))))"
  | .lambdaLambda => "apply((((flag ? lam(x){return x;} : lam(y){return y;}))))"
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
      [⟨outer, .group ⟨middle, .group ⟨inner, .group ⟨is, .conditional
        ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩⟩⟩]⟩⟩ =>
    if h : cs = range file 0 (conditionalStop mode+4) ∧ cas = range file 0 5 ∧ cns = range file 0 5 ∧ as = range file 5 (conditionalStop mode+4) ∧ outer = range file 6 (conditionalStop mode+3) ∧ middle = range file 7 (conditionalStop mode+2) ∧ inner = range file 8 (conditionalStop mode+1) ∧ is = range file 9 (conditionalStop mode) ∧ fs = range file 9 13 ∧ fns = range file 9 13 ∧ q = range file 14 15 ∧ colon = colonRange file mode then
      match mode with
      | .lambdaOrdinary => do
          let y ← exactLambda? file 16 "x" yes; let n ← exactReference? file 36 44 "ordinary" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .ordinaryLambda => do
          let y ← exactReference? file 16 24 "ordinary" yes; let n ← exactLambda? file 27 "x" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
      | .lambdaLambda => do
          let y ← exactLambda? file 16 "x" yes; let n ← exactLambda? file 36 "y" no
          some ⟨by rw [y.down, n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source, thenSource, elseSource, conditionalStop, colonRange, reference]⟩
    else none
  | _ => none
private def callAt (file : Syntax.SourceFile) (stop : Nat) (argument : Syntax.Expr) : Syntax.Expr :=
  ⟨range file 0 stop, .call (reference file 0 5 "apply") ⟨range file 5 stop, [argument]⟩⟩
private def conditionalAt (file : Syntax.SourceFile) (start : Nat) : Syntax.Expr :=
  ⟨range file start (start + 35), .conditional (reference file start (start + 4) "flag")
    (range file (start + 5) (start + 6)) (lambdaAt file (start + 7) "x")
    (range file (start + 25) (start + 26)) (reference file (start + 27) (start + 35) "ordinary")⟩
private inductive ExactControl where | conditional2 | conditional4 | lambda3
private def controlSource (file : Syntax.SourceFile) : ExactControl → Syntax.Expr
  | .conditional2 => callAt file 46 ⟨range file 6 45, .group ⟨range file 7 44, .group (conditionalAt file 8)⟩⟩
  | .conditional4 => callAt file 50 ⟨range file 6 49, .group ⟨range file 7 48, .group ⟨range file 8 47, .group ⟨range file 9 46, .group (conditionalAt file 10)⟩⟩⟩⟩
  | .lambda3 => callAt file 30 ⟨range file 6 29, .group ⟨range file 7 28, .group ⟨range file 8 27, .group (lambdaAt file 9 "x")⟩⟩⟩
private def exactControl? (file : Syntax.SourceFile) (kind : ExactControl) (candidate : Syntax.Expr) : Option (PLift (candidate = controlSource file kind)) :=
  match kind, candidate with
  | .conditional2, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 8 12 "flag" condition; let y ← exactLambda? file 15 "x" yes; let n ← exactReference? file 35 43 "ordinary" no
    if h : cs=range file 0 46 ∧ as=range file 5 46 ∧ o=range file 6 45 ∧ i=range file 7 44 ∧ is=range file 8 43 ∧ q=range file 13 14 ∧ colon=range file 33 34 then some ⟨by rw [c.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .conditional4, ⟨cs, .call callee ⟨as, [⟨a, .group ⟨b, .group ⟨c, .group ⟨d, .group ⟨is, .conditional condition q yes colon no⟩⟩⟩⟩⟩]⟩⟩ => do
    let ca ← exactReference? file 0 5 "apply" callee; let f ← exactReference? file 10 14 "flag" condition; let y ← exactLambda? file 17 "x" yes; let n ← exactReference? file 37 45 "ordinary" no
    if h : cs=range file 0 50 ∧ as=range file 5 50 ∧ a=range file 6 49 ∧ b=range file 7 48 ∧ c=range file 8 47 ∧ d=range file 9 46 ∧ is=range file 10 45 ∧ q=range file 15 16 ∧ colon=range file 35 36 then some ⟨by rw [ca.down,f.down,y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | .lambda3, ⟨cs, .call callee ⟨as, [⟨o, .group ⟨i, .group ⟨j, .group body⟩⟩⟩]⟩⟩ => do
    let c ← exactReference? file 0 5 "apply" callee; let b ← exactLambda? file 9 "x" body
    if h : cs=range file 0 30 ∧ as=range file 5 30 ∧ o=range file 6 29 ∧ i=range file 7 28 ∧ j=range file 8 27 then some ⟨by rw [c.down,b.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0331-{label mode}.sol" (modeText mode)
  let some equality := exactSuccess? file mode parsed | throw (IO.userError s!"{label mode}: exact AST/spans")
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed &&
    child == some (core mode, .word) && previous.isNone && wrapped == child) s!"{label mode}: exact wrapper route"
  proof (equality.down ▸ parsed_three_group_wrapper_static_contract file mode)
  proof (childE file mode).provenance; proof (wrapperE file mode).provenance
  if none : previous = none then proof none else throw (IO.userError s!"{label mode}: predecessor proof")
private def rejected (label text : String) : IO Unit := do
  let (_, parsed) ← parseComplete s!"adr0331-{label}.sol" text
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == child && wrapped.isNone) s!"{label}: selected failure changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = true then
    if childNone : child = none then
      have route := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda?_of_threeLevelGroupedConditional (types := types) (owner := owner) (inputs := inputs) boundary
      proof childNone; proof route; proof (show wrapped = none by simpa only [wrapped, child] using route.trans childNone)
    else throw (IO.userError s!"{label}: child proof")
  else throw (IO.userError s!"{label}: classifier proof")
private def verifyFailures : IO Unit := do
  for (label, text) in [("condition-type", "apply((((wrong ? lam(x){return x;} : ordinary))))"),
      ("condition-missing", "apply((((missing ? lam(x){return x;} : ordinary))))"),
      ("header", "apply((((flag ? lam(x,y){return x;} : ordinary))))"),
      ("body", "apply((((flag ? lam(x){return flag;} : ordinary))))"),
      ("other-type", "apply((((flag ? lam(x){return x;} : wrong))))"),
      ("other-missing", "apply((((flag ? lam(x){return x;} : missing))))"),
      ("nonfunction", "flag((((flag ? lam(x){return x;} : ordinary))))"),
      ("callee-missing", "globalApply((((flag ? lam(x){return x;} : ordinary))))"),
      ("mixed-grouped", "apply((((flag ? lam(x){return x;} : (lam(y){return y;})))))"),
      ("mixed-nested", "apply((((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))))")] do rejected label text
private def preserved (label text : String) (expected : Option (Core.Expr × Core.Ty))
    (expectedAst : Option ExactControl) : IO Unit := do
  let (file, parsed) ← parseComplete s!"adr0331-{label}.sol" text
  match expectedAst with
  | some kind =>
    let some equality := exactControl? file kind parsed | throw (IO.userError s!"{label}: predecessor AST/spans")
    proof equality.down
  | none => pure ()
  let child := elaborateThreeLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed
  let previous := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  let wrapped := elaborateLocalApplicationWithThreeLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (!isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone &&
    wrapped == previous && previous == expected) s!"{label}: complete ADR0329 Option changed"
  if boundary : isThreeLevelGroupedConditionalExpectedLambdaArgumentApplication parsed = false then
    if exact : child = none ∧ previous = expected then
      proof exact.1
      have route := falseRoute (t := types) (o := owner) (i := inputs) boundary
      proof route; proof (show wrapped = expected by simpa only [wrapped, previous] using route.trans exact.2)
      match expected with
      | none => pure ()
      | some result => if accepted : previous = some result then let relation := elaborateLocalApplicationWithTwoLevelGroupedConditionalExpectedLambda?_iff.mp accepted; let wrapperRelation : LocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaElaborates types owner inputs parsed result.1 result.2 := .existing boundary relation; proof relation; proof relation.provenance; proof wrapperRelation; proof wrapperRelation.provenance else throw (IO.userError s!"{label}: relation proof")
    else throw (IO.userError s!"{label}: ADR0329 Option proof")
  else throw (IO.userError s!"{label}: false-route proof")
private def verifyPreservation : IO Unit := do
  let conditionalCore := .apply (.var 0) (.ifE (.var 3) lambdaCore (.var 4))
  preserved "immediate-conditional" "apply(flag ? lam(x){return x;} : ordinary)" (some (conditionalCore, .word)) none
  preserved "one-group-conditional" "apply((flag ? lam(x){return x;} : ordinary))" (some (conditionalCore, .word)) none
  preserved "two-group-conditional" "apply(((flag ? lam(x){return x;} : ordinary)))" (some (conditionalCore, .word)) (some .conditional2)
  preserved "four-group-conditional" "apply(((((flag ? lam(x){return x;} : ordinary)))))" none (some .conditional4)
  preserved "all-ordinary" "apply((((flag ? ordinary : ordinary))))" (some (.apply (.var 0) (.ifE (.var 3) (.var 4) (.var 4)), .word)) none
  for (depth, label, text) in [(0, "direct-lambda", "apply(lam(x){return x;})"),
      (1, "one-lambda-group", "apply((lam(x){return x;}))"),
      (2, "two-lambda-groups", "apply(((lam(x){return x;})))"),
      (3, "three-lambda-groups", "apply((((lam(x){return x;}))))"),
      (4, "four-lambda-groups", "apply(((((lam(x){return x;})))))")] do
    preserved label text (some (.apply (.var 0) lambdaCore, .word))
      (if depth = 3 then some .lambda3 else none)
  preserved "ordinary-singleton" "apply(ordinary)" (some (.apply (.var 0) (.var 4), .word)) none
  for (label, text) in [("grouped-only", "apply((((flag ? (lam(x){return x;}) : ordinary))))"),
      ("nested-only", "apply((((flag ? ordinary(lam(x){return x;}) : ordinary))))"),
      ("tuple", "apply((lam(x){return x;},ordinary))"), ("nested-call", "apply(ordinary(lam(x){return x;}))"),
      ("returned-lambda", "apply((((lam(x){return lam(y){return y;};}))))"), ("inferred-let-lambda", "apply((((lam(x){let y = lam(z){return z;};return x;}))))"),
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
    verifySuccess mode
    for choice in [false, true] do
      runExact (label mode) 13 14 (core mode) choice (by
        have evaluated := independently_executed_three_group_wrapper_core mode choice
          opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
        simpa [environment] using evaluated)
  for choice in [false, true] do
    let conditionalEvidence := independently_executed_three_group_wrapper_core .lambdaOrdinary choice
      opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
    runExact "immediate-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "one-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "two-group-conditional-control" 13 14 (core .lambdaOrdinary) choice (by simpa [environment] using conditionalEvidence)
    runExact "direct-lambda-control" 10 11 directCore choice (directE choice)
    runExact "finite-group-lambda-control" 10 11 directCore choice (directE choice)
  verifyFailures
  verifyPreservation
end Tests.ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent
def Tests.adr0331ParsedLocalApplicationWithThreeLevelGroupedConditionalExpectedLambdaTests : IO Unit := ADR0331ParsedLocalApplicationWithThreeLevelGroupedConditionalConsumerIndependent.exercise *> IO.println "ADR0331 parsed local three-level grouped conditional wrapper GREEN"
