import Solcore.Frontend.RuntimeValue
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests
namespace ParsedRuntimeClosureValues
open Solcore Solcore.Frontend

/- Only inert representation data is constructed here: no source evaluation, typing or admission. -/
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def verify {α : Type} [DecidableEq α] (actual expected : α)
    (_exact : actual = expected) (label : String) : IO Unit := check (decide (actual = expected)) label
private def fileId : Syntax.SourceId := ⟨.main,"runtime-closure-values.sol"⟩
private def span (first last : Nat) : Syntax.SourceSpan := ⟨fileId,first,last⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"RuntimeClosureValues",by decide⟩],by decide⟩⟩,152⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner,index⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : List (String × Resolved.LocalId) :=
  [("x",id 7),("x",id 31),("foreign",foreign),("orphan",id 99)]
private def captures : List (Resolved.LocalId × RuntimeValue) :=
  [(id 31,.word (word 41)),(id 7,.bool true),
    (id 31,.coreClosure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
    (foreign,.pair (.word (word 17)) .unit),(id 777,.cellRef .word 1)]
private def packed (source : Syntax.Expr) : RuntimeValue := .sourceClosure source owner names captures
private theorem original_data (source : Syntax.Expr) :
    match packed source with
    | .sourceClosure actual actualOwner actualNames actualCaptures =>
        actual = source ∧ actualOwner = owner ∧ actualNames = names ∧ actualCaptures = captures
    | _ => False := ⟨rfl,rfl,rfl,rfl⟩
private theorem literal_rows : names.map Prod.snd = [id 7,id 31,foreign,id 99] ∧
    captures.map Prod.fst = [id 31,id 7,id 31,foreign,id 777] ∧
    names.length ≠ captures.length := by decide
private theorem captured_payloads : captures.map (fun row => row.2.toCore?) =
    [some (.word (word 41)),some (.bool true),
      some (.closure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
      some (.pair (.word (word 17)) .unit),some (.cellRef .word 1)] := by
  simp [captures,RuntimeValue.toCore?]
private def blocked (source : Syntax.Expr) : List RuntimeValue :=
  let value := packed source
  [value,.pair value .unit,.pair (.bool false) value,
    .inLeft (.namedData ⟨777⟩) value,.inRight (.cell (.function .word .word)) value,
    .constructed ⟨⟨777⟩,888⟩ value,
    .coreClosure .word .word (.word Core.Word.zero) [.unit,value,.bool true],
    .coreClosure .unit .unit (.var 99) [.pair .unit (.coreClosure .unit .unit .unit [value])],
    .sourceClosure source {owner with declarationIndex:=901} [] [(foreign,value)]]
private theorem blocked_exact (source : Syntax.Expr) :
    (blocked source).map RuntimeValue.toCore? = List.replicate 9 none := by
  simp [blocked,packed,RuntimeValue.toCore?]
private def mixedStore (source : Syntax.Expr) : List RuntimeValue :=
  [.word (word 17),packed source,.cellRef .word 1]
private theorem stored_exact (source : Syntax.Expr) :
    (mixedStore source).mapM RuntimeValue.toCore? = none ∧
    ((mixedStore source)[1]?).map RuntimeValue.toCore? = some none ∧
    (RuntimeValue.cellRef .word 1).toCore? = some (.cellRef .word 1) := by
  simp [mixedStore,packed,RuntimeValue.toCore?]
private theorem not_old_image (source : Syntax.Expr) (core : Core.Value) : packed source ≠ .ofCore core := by
  intro equality
  have projected := RuntimeValue.toCore?_eq_some_iff.mpr equality
  simp [packed,RuntimeValue.toCore?] at projected
private def oldValues : List Core.Value :=
  [.unit,.bool false,.word (word 41),.hostFunction .callContractWordWithValue,
    .pair (.word (word 17)) (.bool true),
    .closure (.cell (.function .word .word)) (.namedData ⟨777⟩) (.var 99)
      [.bool true,.closure .bool .unit (.var 400) [.cellRef .word 700],.word (word 41)],
    .inLeft (.namedData ⟨777⟩) (.bool true),.inRight (.cell .word) (.word (word 17)),
    .cellRef (.function .word .word) 900,.constructed ⟨⟨777⟩,888⟩ (.pair .unit (.bool false))]

private def typeName (name : String) (first last : Nat) : Syntax.TypeExpr :=
  ⟨span first last,.named ⟨span first last,⟨⟨⟨span first last,name⟩,[]⟩⟩⟩ none⟩
private def identifier (name : String) (first last : Nat) : Syntax.Expr :=
  ⟨span first last,.identifier ⟨span first last,name⟩⟩
private def richText := "lam(x:A)->B{let x:A=x;return saved;}"
/- An independent complete syntax literal, including the original shadowing initializer and tail. -/
private def richOriginal : Syntax.Expr :=
  ⟨span 0 36,.lambda (span 0 3)
    ⟨span 3 8,[⟨span 4 7,.typed none ⟨span 4 5,"x"⟩ (typeName "A" 6 7)⟩]⟩
    (some (typeName "B" 10 11))
    ⟨span 11 36,[⟨span 12 22,.letDecl ⟨span 16 17,"x"⟩
      (some (typeName "A" 18 19)) (some (identifier "x" 20 21))⟩,
      ⟨span 22 35,.returnStmt (some (identifier "saved" 29 34))⟩]⟩⟩
private def parameterTag (parameter : Syntax.LambdaParameter) : String :=
  match parameter.value with
  | .inferred name => "inferred:" ++ name.value
  | .typed marker name _ => (if marker.isSome then "marked:" else "typed:") ++ name.value
  | .error => "error"
private def shape (source : Syntax.Expr) : String :=
  match source.value with
  | .lambda _ parameters returns _ =>
      "lambda " ++ reprStr (parameters.elements.map parameterTag) ++
        (if returns.isSome then " annotated" else " omitted")
  | .identifier name => "identifier:" ++ name.value
  | .call _ _ => "call"
  | .group _ => "group"
  | .error => "error"
  | _ => "other"
private def parsed (text : String) (expected : String) (diagnostics : Nat) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨fileId,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd &&
        decide (source.span = Syntax.SourceSpan.fullFile file)) "complete original expression span"
      check (decide (shape source = expected ∧ next.diagnostics.length = diagnostics)) "actual AST and diagnostics"
      if let .lambda keyword parameters returns body := source.value then
        check (source.span.contains keyword && source.span.contains parameters.span &&
          source.span.contains body.span && parameters.elements.all (fun p => parameters.span.contains p.span) &&
          returns.toList.all (fun annotation => source.span.contains annotation.span) &&
          body.value.all (fun statement => body.span.contains statement.span)) "unchanged nested source spans"
      return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspect (text : String) (expected : String) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text expected diagnostics
  if text = richText then check (source == richOriginal) "independent full original syntax literal"
  match valueEq : packed source with
  | .sourceClosure actual actualOwner actualNames actualCaptures =>
      have saved : actual = source ∧ actualOwner = owner ∧ actualNames = names ∧ actualCaptures = captures := by
        simpa only [valueEq] using original_data source
      check (actual == source) "the complete original Expr is retained, including error and nonlambda data"
      verify actual.span source.span (congrArg Syntax.Located.span saved.1) "literal source span"
      verify actualOwner owner saved.2.1 "owner is not recomputed from the source or capture IDs"
      verify actualNames names saved.2.2.1 "ordered duplicate names are not normalized"
      check (decide (actualNames.length ≠ actualCaptures.length)) "no name/capture alignment premise"
      verify (actualCaptures.map Prod.fst) [id 31,id 7,id 31,foreign,id 777]
        (by simpa only [saved.2.2.2] using literal_rows.2.1) "ordered duplicate, foreign and environment-only capture IDs"
      verify (actualCaptures.map (fun row => row.2.toCore?))
        [some (.word (word 41)),some (.bool true),
          some (.closure .word .unit (.var 99) [.cellRef .word 700,.bool false]),
          some (.pair (.word (word 17)) .unit),some (.cellRef .word 1)]
        (by simpa only [saved.2.2.2] using captured_payloads) "all actual capture payloads, tags and Core code"
  | _ => throw (IO.userError "original source data constructor changed")
  verify ((blocked source).map RuntimeValue.toCore?) (List.replicate 9 none)
    (blocked_exact source) "source data nested in pairs, sums, data, unused Core captures and source captures"
  verify ((mixedStore source).mapM RuntimeValue.toCore?) none (stored_exact source).1 "raw mixed-store projection"
  verify (((mixedStore source)[1]?).map RuntimeValue.toCore?) (some none)
    (stored_exact source).2.1 "actual referenced slot is nonprojectable"
  verify (RuntimeValue.cellRef .word 1).toCore? (some (.cellRef .word 1))
    (stored_exact source).2.2 "cell reference projection does not follow that raw store"
  have noReplacement : ∀ core, packed source ≠ RuntimeValue.ofCore core := not_old_image source
  have noCore : ¬ ∃ core, (packed source).toCore? = some core := by
    rintro ⟨core,projected⟩
    exact noReplacement core (RuntimeValue.toCore?_eq_some_iff.mp projected)
  check (decide ((packed source).toCore? = none)) "inert source cannot be replaced with an invented Core closure"
  have _ : ¬ ∃ core, (packed source).toCore? = some core := noCore
end ParsedRuntimeClosureValues

open ParsedRuntimeClosureValues in
/-- Parsed code and lexical metadata are inert data; this test claims no source execution or typing. -/
def frontendParsedRuntimeClosureValueTests : IO Unit := do
  for core in oldValues do
    verify (Solcore.Frontend.RuntimeValue.ofCore core).toCore? (some core)
      (Solcore.Frontend.RuntimeValue.toCore?_ofCore core)
      "every old constructor is in the exact embedding image, regardless of runtime validity"
    match projected : (Solcore.Frontend.RuntimeValue.ofCore core).toCore? with
    | some actual =>
        have image := Solcore.Frontend.RuntimeValue.toCore?_eq_some_iff.mp projected
        verify actual core (Solcore.Frontend.RuntimeValue.ofCore_injective image.symm)
          "successful projection reflects the exact image and injectivity recovers the original value"
    | none => throw (IO.userError "embedded Core data lost its projection")
  do
    inspect "lam(x){return x;}" "lambda [\"inferred:x\"] omitted"
    inspect richText "lambda [\"typed:x\"] annotated"
    inspect "lam(x,)->A{return saved;}" "lambda [\"inferred:x\"] annotated"
    inspect "lam(){return saved;}" "lambda [] omitted"
    inspect "lam(x,y){return x;}" "lambda [\"inferred:x\", \"inferred:y\"] omitted"
    inspect "lam(comptime x:A){return x;}" "lambda [\"marked:x\"] omitted"
    inspect "lam(comptime){return comptime;}" "lambda [\"inferred:comptime\"] omitted" 1
    inspect "lam(comptime:A){return comptime;}" "lambda [\"typed:comptime\"] omitted" 1
    inspect "lam(comptime x){return x;}" "lambda [\"error\"] omitted" 1
    inspect "lam(x){let ;}" "lambda [\"inferred:x\"] omitted" 1
    inspect "lam(x:Missing)->Missing{return absent;}" "lambda [\"typed:x\"] annotated"
    inspect "lam(x){return lam(y){return x;};}" "lambda [\"inferred:x\"] omitted"
    inspect "saved" "identifier:saved"
    inspect "saved(x)" "call"
    inspect "(lam(x){return x;})" "group"
    inspect "let" "error" 2

end Tests
