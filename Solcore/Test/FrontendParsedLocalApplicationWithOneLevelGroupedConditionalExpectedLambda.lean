import Solcore.Frontend.LocalApplication
import Solcore.Core.Correspondence
import Solcore.Syntax.Parser.Term
/-! Parsed consumer for grouped-conditional-first local application dispatch. -/
set_option autoImplicit false
namespace Tests.ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent
open Solcore Solcore.Frontend
private def check (condition : Bool) (message : String) : IO Unit := unless condition do throw (IO.userError message)
private def proof {proposition : Prop} (_ : proposition) : IO Unit := pure ()
private inductive Mode where | lambdaOrdinary | ordinaryLambda | lambdaLambda
private inductive Existing where | conditional | depthTwo | depthThree
private def declaration (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ParsedUnifiedGroupedConditional", by decide⟩], by decide⟩⟩, index⟩
private def owner := declaration 327
private def foreignOwner := declaration 9327
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
  ⟨range file start (start+17), .lambda (range file start (start+3)) ⟨range file (start+3) (start+6),
    [⟨range file (start+4) (start+5), .inferred ⟨range file (start+4) (start+5), name⟩⟩]⟩ none
    ⟨range file (start+6) (start+17), [⟨range file (start+7) (start+16),
      .returnStmt (some (reference file (start+14) (start+15) name))⟩]⟩⟩
private def thenSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary | .lambdaLambda => lambdaAt file 14 "x" | .ordinaryLambda => reference file 14 22 "ordinary"
private def elseSource (file : Syntax.SourceFile) : Mode → Syntax.Expr
  | .lambdaOrdinary => reference file 34 42 "ordinary" | .ordinaryLambda => lambdaAt file 25 "x" | .lambdaLambda => lambdaAt file 34 "y"
private def colonRange (file : Syntax.SourceFile) : Mode → Syntax.SourceSpan
  | .lambdaOrdinary | .lambdaLambda => range file 32 33 | .ordinaryLambda => range file 23 24
private def conditionalStop : Mode → Nat | .lambdaLambda => 51 | _ => 42
private def source (file : Syntax.SourceFile) (mode : Mode) : Syntax.Expr :=
  let stop := conditionalStop mode
  ⟨range file 0 (stop+2), .call (reference file 0 5 "apply") ⟨range file 5 (stop+2),
    [⟨range file 6 (stop+1), .group ⟨range file 7 stop, .conditional (reference file 7 11 "flag")
      (range file 12 13) (thenSource file mode) (colonRange file mode) (elseSource file mode)⟩⟩]⟩⟩
private def existingSource (file : Syntax.SourceFile) : Existing → Syntax.Expr
  | .conditional => ⟨range file 0 42, .call (reference file 0 5 "apply") ⟨range file 5 42,
      [⟨range file 6 41, .conditional (reference file 6 10 "flag") (range file 11 12)
        (lambdaAt file 13 "x") (range file 31 32) (reference file 33 41 "ordinary")⟩]⟩⟩
  | .depthTwo => ⟨range file 0 28, .call (reference file 0 5 "apply") ⟨range file 5 28,
      [⟨range file 6 27, .group ⟨range file 7 26, .group (lambdaAt file 8 "x")⟩⟩]⟩⟩
  | .depthThree => ⟨range file 0 30, .call (reference file 0 5 "apply") ⟨range file 5 30,
      [⟨range file 6 29, .group ⟨range file 7 28, .group ⟨range file 8 27,
        .group (lambdaAt file 9 "x")⟩⟩⟩]⟩⟩
private def lambdaCore : Core.Expr := .lambda .word .word (.var 0)
private def thenCore : Mode → Core.Expr | .lambdaOrdinary | .lambdaLambda => lambdaCore | .ordinaryLambda => .var 4
private def elseCore : Mode → Core.Expr | .lambdaOrdinary => .var 4 | .ordinaryLambda | .lambdaLambda => lambdaCore
private def conditionalCore (mode : Mode) : Core.Expr := .apply (.var 0) (.ifE (.var 3) (thenCore mode) (elseCore mode))
private def groupedCore : Core.Expr := .apply (.var 0) lambdaCore
private theorem calleeE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 0 5 "apply") (.var 0) (.function functionType .word) := .pure (.identifier .head) (.var .head) (.var .head)
private theorem flagE (file : Syntax.SourceFile) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file 7 11 "flag") (.var 3) .bool :=
  .pure (.identifier (.tail (by change "apply" ≠ "flag"; decide) (.tail (by change "opaque" ≠ "flag"; decide) (.tail (by change "apply" ≠ "flag"; decide) .head))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
private theorem ordinaryE (file : Syntax.SourceFile) (start stop : Nat) : RecursiveLocalComputationElaborates inputs.names inputs.context (reference file start stop "ordinary") (.var 4) functionType :=
  .pure (.identifier (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "opaque" ≠ "ordinary"; decide) (.tail (by change "apply" ≠ "ordinary"; decide) (.tail (by change "flag" ≠ "ordinary"; decide) .head)))))
    (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
private theorem lambdaE (file : Syntax.SourceFile) (start : Nat) (name : String) : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner inputs (lambdaAt file start name) lambdaCore functionType := by
  apply ExpectedComputationLambdaElaborates.lambda (header := ⟨inputs.bindFresh owner name .word,
    ⟨range file (start+6) (start+17), [⟨range file (start+7) (start+16), .returnStmt (some (reference file (start+14) (start+15) name))⟩]⟩, .word, .word⟩)
  · exact ExpectedUnaryLambdaHeaderDeclares.lambda ExpectedLambdaParameterDeclares.inferred ExpectedLambdaReturnDenotes.omitted
  · exact .word
  · exact .word
  · exact ComputationReturnTreeElaborates.expression (.pure (.identifier .head) (.var .head) (.var .head))
private theorem thenE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (thenSource file mode) (thenCore mode) := by
  cases mode with | lambdaOrdinary => exact .expected rfl (lambdaE file 14 "x") | ordinaryLambda => exact .ordinary rfl (ordinaryE file 14 22) | lambdaLambda => exact .expected rfl (lambdaE file 14 "x")
private theorem elseE (file : Syntax.SourceFile) (mode : Mode) : ConditionalExpectedLambdaBranchElaborates types owner inputs functionType (elseSource file mode) (elseCore mode) := by
  cases mode with | lambdaOrdinary => exact .ordinary rfl (ordinaryE file 34 42) | ordinaryLambda => exact .expected rfl (lambdaE file 25 "x") | lambdaLambda => exact .expected rfl (lambdaE file 34 "y")
private theorem sourceE (file : Syntax.SourceFile) (mode : Mode) : OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (conditionalCore mode) .word := by
  cases mode <;> exact .application rfl (calleeE file) (flagE file) (thenE file _) (elseE file _)
private theorem oldBoundaries (file : Syntax.SourceFile) (mode : Mode) : isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false := by
  constructor
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro selected
    obtain ⟨_,_,_,_,_,spine⟩ := isThreeOrMoreGroupedExpectedLambdaArgumentApplication_iff.mp selected
    cases spine with | group child => cases child
private theorem wrapperE (file : Syntax.SourceFile) (mode : Mode) : LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (conditionalCore mode) .word := .oneLevelGroupedConditional (sourceE file mode).classified (sourceE file mode)
/-- Parsed new sources and every old source retain the complete selected child Option. -/
theorem parsed_unified_static_contract (file : Syntax.SourceFile) (mode : Mode) :
    OneLevelGroupedConditionalExpectedLambdaArgumentApplicationElaborates types owner inputs (source file mode) (conditionalCore mode) .word ∧
    LocalApplicationWithOneLevelGroupedConditionalExpectedLambdaElaborates types owner inputs (source file mode) (conditionalCore mode) .word ∧
    isOneLevelGroupedConditionalExpectedLambdaArgumentApplication (source file mode) = true ∧
    elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs (source file mode) = some (conditionalCore mode, .word) ∧
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs (source file mode) = some (conditionalCore mode, .word) ∧
    isConditionalExpectedLambdaArgumentApplication (source file mode) = false ∧ isThreeOrMoreGroupedExpectedLambdaArgumentApplication (source file mode) = false ∧
    Core.HasType inputs.context.values (conditionalCore mode) .word ∧
    ∀ old, isOneLevelGroupedConditionalExpectedLambdaArgumentApplication old = false →
      elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs old = elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs old := by
  have child := sourceE file mode; have wrapped := wrapperE file mode; have old := oldBoundaries file mode
  exact ⟨child, wrapped, child.classified, elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication?_iff.mpr child,
    elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_iff.mpr wrapped, old.1, old.2,
    wrapped.core_hasType, fun _ boundary => elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing boundary⟩
private def seven : Core.Word := Core.Word.ofNatModulo 7
private def opaqueValue : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef (.function .word .unit) 700]
private def applyValue : Core.Value := .closure functionType .word (.apply (.var 0) (.word seven)) [opaqueValue, .hostFunction .storageWrite]
private def ordinaryValue : Core.Value := .closure .word .word (.var 0) [.hostFunction .storageRead]
private def environment (choice : Bool) : Core.Environment := [applyValue, opaqueValue, .cellRef (.function .unit .word) 31, .bool choice, ordinaryValue, .word seven]
private def store : Core.Store := [opaqueValue, .cellRef (.function .word .word) 23, .hostFunction .storageWrite]
/-- Conditional and grouped-lambda child Cores execute independently with exact store preservation. -/
theorem independently_executed_wrapper_cores (mode : Mode) (choice : Bool) (opaqueRow duplicateRow wrongRow : Core.Value) (initialStore : Core.Store) :
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow] initialStore (conditionalCore mode) (.word seven) initialStore ∧
    Core.Evaluates [applyValue, opaqueRow, duplicateRow, .bool choice, ordinaryValue, wrongRow] initialStore groupedCore (.word seven) initialStore := by
  constructor
  · cases mode <;> cases choice
    · exact .apply (.var rfl) (.ifFalse (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) (.var rfl)) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifFalse (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
    · exact .apply (.var rfl) (.ifTrue (.var rfl) .lambda) (.apply (.var rfl) .word (.var rfl))
  · exact .apply (.var rfl) .lambda (.apply (.var rfl) .word (.var rfl))
private def modeText : Mode → String | .lambdaOrdinary => "apply((flag ? lam(x){return x;} : ordinary))" | .ordinaryLambda => "apply((flag ? ordinary : lam(x){return x;}))" | .lambdaLambda => "apply((flag ? lam(x){return x;} : lam(y){return y;}))"
private def existingText : Existing → String | .conditional => "apply(flag ? lam(x){return x;} : ordinary)" | .depthTwo => "apply(((lam(x){return x;})))" | .depthThree => "apply((((lam(x){return x;}))))"
private def label : Mode → String | .lambdaOrdinary => "lambda-ordinary" | .ordinaryLambda => "ordinary-lambda" | .lambdaLambda => "lambda-lambda"
private def parseComplete (path text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main, path⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError s!"{path}: lexer")
  check lexed.diagnostics.isEmpty s!"{path}: lexer diagnostics"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok parsed next => check (next.diagnostics.isEmpty && next.atEnd && parsed.span == Syntax.SourceSpan.fullFile file) s!"{path}: parser/EOF/span"; pure (file, parsed)
  | _ => throw (IO.userError s!"{path}: parser")
private def exactReference? (file : Syntax.SourceFile) (start stop : Nat) (name : String) (candidate : Syntax.Expr) : Option (PLift (candidate = reference file start stop name)) :=
  match candidate with | ⟨span, .identifier ⟨nameSpan, observed⟩⟩ => if h : span = range file start stop ∧ nameSpan = range file start stop ∧ observed = name then some ⟨by rcases h with ⟨rfl,rfl,rfl⟩; rfl⟩ else none | _ => none
private def exactLambda? (file : Syntax.SourceFile) (start : Nat) (name : String) (candidate : Syntax.Expr) : Option (PLift (candidate = lambdaAt file start name)) :=
  match candidate with
  | ⟨ls, .lambda ks ⟨ps, [⟨p, .inferred ⟨pn, observed⟩⟩]⟩ none ⟨bs, [⟨ss, .returnStmt (some ⟨rs, .identifier ⟨rn, result⟩⟩)⟩]⟩⟩ =>
    if h : ls=range file start (start+17) ∧ ks=range file start (start+3) ∧ ps=range file (start+3) (start+6) ∧ p=range file (start+4) (start+5) ∧ pn=range file (start+4) (start+5) ∧ observed=name ∧ bs=range file (start+6) (start+17) ∧ ss=range file (start+7) (start+16) ∧ rs=range file (start+14) (start+15) ∧ rn=range file (start+14) (start+15) ∧ result=name then some ⟨by rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩ else none
  | _ => none
private def exactSource? (file : Syntax.SourceFile) (mode : Mode) (candidate : Syntax.Expr) : Option (PLift (candidate = source file mode)) :=
  match candidate with
  | ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as, [⟨gs, .group ⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩⟩]⟩⟩ =>
    if h : cs=range file 0 (conditionalStop mode+2) ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 (conditionalStop mode+2) ∧ gs=range file 6 (conditionalStop mode+1) ∧ is=range file 7 (conditionalStop mode) ∧ fs=range file 7 11 ∧ fns=range file 7 11 ∧ q=range file 12 13 ∧ colon=colonRange file mode then
      match mode with
      | .lambdaOrdinary => do let y ← exactLambda? file 14 "x" yes; let n ← exactReference? file 34 42 "ordinary" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
      | .ordinaryLambda => do let y ← exactReference? file 14 22 "ordinary" yes; let n ← exactLambda? file 25 "x" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
      | .lambdaLambda => do let y ← exactLambda? file 14 "x" yes; let n ← exactLambda? file 34 "y" no; some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; simp [source,thenSource,elseSource,conditionalStop,colonRange,reference]⟩
    else none
  | _ => none
private def exactExisting? (file : Syntax.SourceFile) (route : Existing) (candidate : Syntax.Expr) : Option (PLift (candidate = existingSource file route)) :=
  match route, candidate with
  | .conditional, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨is, .conditional ⟨fs, .identifier ⟨fns, "flag"⟩⟩ q yes colon no⟩]⟩⟩ =>
    if h : cs=range file 0 42 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 42 ∧ is=range file 6 41 ∧ fs=range file 6 10 ∧ fns=range file 6 10 ∧ q=range file 11 12 ∧ colon=range file 31 32 then do
      let y ← exactLambda? file 13 "x" yes; let n ← exactReference? file 33 41 "ordinary" no
      some ⟨by rw [y.down,n.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | .depthTwo, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨outer, .group ⟨inner, .group term⟩⟩]⟩⟩ =>
    if h : cs=range file 0 28 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 28 ∧ outer=range file 6 27 ∧ inner=range file 7 26 then do
      let child ← exactLambda? file 8 "x" term
      some ⟨by rw [child.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | .depthThree, ⟨cs, .call ⟨cas, .identifier ⟨cns, "apply"⟩⟩ ⟨as,
      [⟨first, .group ⟨second, .group ⟨third, .group term⟩⟩⟩]⟩⟩ =>
    if h : cs=range file 0 30 ∧ cas=range file 0 5 ∧ cns=range file 0 5 ∧ as=range file 5 30 ∧ first=range file 6 29 ∧ second=range file 7 28 ∧ third=range file 8 27 then do
      let child ← exactLambda? file 9 "x" term
      some ⟨by rw [child.down]; rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩; rfl⟩
    else none
  | _, _ => none
private def verifySuccess (mode : Mode) : IO Unit := do
  let (file,parsed) ← parseComplete s!"adr0327-{label mode}.sol" (modeText mode)
  let some eq := exactSource? file mode parsed | throw (IO.userError "new exact AST/spans")
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed == some (conditionalCore mode,.word) && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == some (conditionalCore mode,.word)) s!"{label mode}: new route"
  proof (eq.down ▸ parsed_unified_static_contract file mode); proof (sourceE file mode).provenance; proof (wrapperE file mode).provenance
private def verifyExisting (route : Existing) : IO Unit := do
  let (file,parsed) ← parseComplete "adr0327-existing.sol" (existingText route)
  let some eq := exactExisting? file route parsed | throw (IO.userError "existing exact AST/spans")
  let expected := match route with | .conditional => some (conditionalCore .lambdaOrdinary,.word) | .depthTwo | .depthThree => some (groupedCore,.word)
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == expected && elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed == expected) "existing exact Option"
  proof eq.down
  proof (elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda?_of_existing
    (types := types) (owner := owner) (inputs := inputs) (source := existingSource file route)
    (by cases route <;> rfl))
private def rejected (label text : String) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text
  let child := elaborateOneLevelGroupedConditionalExpectedLambdaArgumentApplication? types owner inputs parsed; let wrapped := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed
  check (isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && child.isNone && wrapped.isNone && wrapped == child) s!"{label}: selected failure"
private def inheritedFailure (label text : String) (conditional grouped : Bool) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text; let wrapped := elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed; let old := elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && isConditionalExpectedLambdaArgumentApplication parsed == conditional && isThreeOrMoreGroupedExpectedLambdaArgumentApplication parsed == grouped && wrapped.isNone && wrapped == old) s!"{label}: inherited failure"
private def verifyFailures : IO Unit := do
  for (label,text) in [("condition-type","apply((wrong ? lam(x){return x;} : ordinary))"),("condition-missing","apply((missing ? lam(x){return x;} : ordinary))"),("header","apply((flag ? lam(x,y){return x;} : ordinary))"),("body","apply((flag ? lam(x){return flag;} : ordinary))"),("other-type","apply((flag ? lam(x){return x;} : wrong))"),("other-missing","apply((flag ? lam(x){return x;} : missing))"),("nonfunction","flag((flag ? lam(x){return x;} : ordinary))"),("mixed-grouped","apply((flag ? lam(x){return x;} : (lam(y){return y;})))"),("mixed-nested","apply((flag ? lam(x){return x;} : ordinary(lam(y){return y;})))"),("callee-missing","globalApply((flag ? lam(x){return x;} : ordinary))")] do rejected label text
  inheritedFailure "old-conditional" "apply(flag ? lam(x,y){return x;} : ordinary)" true false
  inheritedFailure "old-grouped" "apply((((lam(x,y){return x;}))))" false true
private def preserved (label text : String) : IO Unit := do
  let (_,parsed) ← parseComplete s!"adr0327-{label}.sol" text
  check (!isOneLevelGroupedConditionalExpectedLambdaArgumentApplication parsed && elaborateLocalApplicationWithOneLevelGroupedConditionalExpectedLambda? types owner inputs parsed == elaborateLocalApplicationWithConditionalAndFiniteGroupedExpectedLambda? types owner inputs parsed) s!"{label}: predecessor Option"
private def verifyPreservation : IO Unit := do
  for route in [Existing.conditional,.depthTwo,.depthThree] do verifyExisting route
  for (label,text) in [("direct","apply(lam(x){return x;})"),("one-group","apply((lam(x){return x;}))"),("ordinary","apply(ordinary)"),("all-ordinary","apply((flag ? ordinary : ordinary))"),("branch-grouped","apply(flag ? (lam(x){return x;}) : ordinary)"),("two-outer","apply(((flag ? lam(x){return x;} : ordinary)))"),("zero","apply()"),("multi","apply(lam(x){return x;},ordinary)"),("top","(flag ? lam(x){return x;} : ordinary)"),("tuple","apply((lam(x){return x;},ordinary))"),("nested","apply(ordinary(lam(x){return x;}))")] do preserved label text
private def runExact (below complete : Nat) (core : Core.Expr) (choice : Bool) (expected : Core.Evaluates (environment choice) store core (.word seven) store) : IO Unit := do
  match Core.runStateful below (Core.State.initial core (environment choice) store) with | .outOfFuel _ => pure () | _ => throw (IO.userError "completed early")
  match actual : Core.runStateful complete (Core.State.initial core (environment choice) store) with
  | .done value finalStore => check (value == .word seven && finalStore == store) "result/store"; proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound actual) expected)
  | .outOfFuel _ => throw (IO.userError "out at boundary") | .fault _ _ => throw (IO.userError "fault")
private def exercise : IO Unit := do
  for mode in [Mode.lambdaOrdinary,.ordinaryLambda,.lambdaLambda] do
    verifySuccess mode
    for choice in [false,true] do
      let evidence := independently_executed_wrapper_cores mode choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store
      runExact 13 14 (conditionalCore mode) choice (by simpa [environment] using evidence.1)
  for choice in [false,true] do let evidence := independently_executed_wrapper_cores .lambdaOrdinary choice opaqueValue (.cellRef (.function .unit .word) 31) (.word seven) store; runExact 10 11 groupedCore choice (by simpa [environment] using evidence.2)
  verifyFailures; verifyPreservation
end Tests.ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent
/-- Run all parsed ADR-0327 grouped-conditional-first checks. -/
def Tests.adr0327ParsedLocalApplicationWithOneLevelGroupedConditionalExpectedLambdaTests : IO Unit := do
  ADR0327ParsedGroupedConditionalFirstWrapperConsumerIndependent.exercise
  IO.println "ADR0327 parsed grouped-conditional-first consumer GREEN"
