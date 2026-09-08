import Solcore.Syntax.Parser.Function
import Solcore.Frontend.StructuralTypeTableProperties
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionCompilation

/-! Complete type occurrences carry independent source meaning, not a type
computed by the tested interpreter. Existing entry gates remain named-only. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedStructuralTypes
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "structural-type.sol"⟩, content⟩
private def parsed? (content : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "complete original type range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (content : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete type: {content}")
  return source
private structure Certificate (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes table source type
private def certify (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Certificate table source) := do
  match sourceAt : source with
  | ⟨_, .named name none⟩ =>
      match found : table.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent name missing")
      | some type => return ⟨type, by rw [sourceAt]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← certify table child
      return ⟨inner.type, by rw [sourceAt]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← certify table left
      let second ← certify table right
      return ⟨.product first.type second.type, by rw [sourceAt]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "outside independent structural certificate")
termination_by sizeOf source
private def checked (content : String) (table : TypeNameTable) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed content
  let independent ← certify table source
  assertTrue (decide (independent.type = expected)) "independent ordered type differs from fixture"
  have accepted := independent.meaning.complete
  have _ := interpretStructuralType?_sound accepted
  have _ := interpretStructuralType?_iff.mpr independent.meaning
  have _ := independent.meaning.type_unique (interpretStructuralType?_sound accepted)
  assertTrue (decide (interpretStructuralType? table source = some expected)) "structural interpretation differs from fixture"
  match source.value with
  | .named _ none =>
      assertTrue (decide (interpretTypeName? table source = some expected)) "named-only compatibility changed"
  | _ => assertTrue (interpretTypeName? table source).isNone "old named-only scope silently broadened"
  let otherSpan : Syntax.SourceSpan := ⟨⟨.external "unrelated", "raw"⟩, 92, 1⟩
  have _ := interpretStructuralType?_span table source otherSpan
  assertTrue (decide (interpretStructuralType? table { source with span := otherSpan } = some expected)) "meaning required outer range validity"
  let extras : TypeNameTable := [(["Word"], .unit), (["Unknown"], .bool)]
  have extended := independent.meaning.extend_types (TypeNameTable.Extends.append_right table extras)
  have _ := interpretStructuralType?_some_of_extends (TypeNameTable.Extends.append_right table extras) accepted
  assertTrue (decide (interpretStructuralType? (table ++ extras) source = some expected)) "later duplicates overrode an accepted nested leaf"
  have _ := extended.complete
  return source
private def table : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["PairAlias"], .product .word .bool), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word)]
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypeGate", by decide⟩], by decide⟩⟩, 23⟩
private def w : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo 9), .word⟩
private def b : TypedRuntimeArgument := ⟨.bool, .bool true, .bool⟩
private def u : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def p : TypedRuntimeArgument := ⟨.product .word .bool, .pair w.value b.value, .pair .word .bool⟩
private def oldGateRejected (content : String) (arguments : List TypedRuntimeArgument)
    (expected : Core.Ty) : IO Unit := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "entry lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete gate declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && lexed.diagnostics.isEmpty &&
    decide (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "gate source lost original completion or range"
  let annotations := source.value.signature.parameters.elements.filterMap (fun parameter =>
    match parameter.value with | .typed none _ annotation => some annotation | _ => none)
  let annotations := annotations ++ (source.value.signature.returnsClause.map (·.types.elements)).getD []
  let annotations := annotations ++ source.value.body.value.filterMap (fun statement =>
    match statement.value with | .letDecl _ (some annotation) _ => some annotation | _ => none)
  let structural := annotations.filter fun annotation => match annotation.value with | .tuple _ => true | _ => false
  let [annotation] := structural | throw (IO.userError "expected one original structural annotation")
  let independent ← certify table annotation
  assertTrue (decide (independent.type = expected ∧ interpretStructuralType? table annotation = some expected))
    "new structural meaning did not come from the original declaration annotation"
  have _ := independent.meaning.complete
  assertTrue (interpretTypeName? table annotation).isNone "old annotation adapter broadened"
  assertTrue (compileRuntimeFunction? table owner source).isNone "old static declaration gate broadened"
  assertTrue (prepareRuntimeFunction? table owner source arguments).isNone "old argument gate broadened"
  assertTrue (evaluateRuntimeFunctionWithCost? table owner source arguments).isNone "old direct entry gate broadened"
  for store in [[], [w.value, .cellRef .word 99]] do
    for fuel in [0, 1, 40] do
      assertTrue (runRuntimeFunction? table owner source arguments fuel store).isNone "rejected gate exposed execution"
end ParsedStructuralTypes
open ParsedStructuralTypes

def frontendParsedStructuralTypeTests : IO Unit := do
  for (left, right) in [(Core.Ty.word, Core.Ty.bool), (.namedData ⟨83⟩, .cell .word),
      (.function .word .bool, .product .unit .bool)] do
    let caller : TypeNameTable := [(["Word"], left), (["Word"], .unit), (["Bool"], right)]
    for text in ["Word", "(Word)", "(Word,)", "((Word,),)"] do let _ ← checked text caller left
    for text in ["()", "(())", "((),)"] do let _ ← checked text caller .unit
    for text in ["(Word,Bool)", "(Word,Bool,)", "((Word,),(Bool,),)"] do
      let _ ← checked text caller (.product left right)
    let _ ← checked "(Bool,Word)" caller (.product right left)
    let _ ← checked "((Word,Bool),())" caller (.product (.product left right) .unit)
    let _ ← checked "(Word,(Bool,()))" caller (.product left (.product right .unit))
    for depth in [0, 1, 3, 6] do
      let text := (List.range depth).foldl (fun inner _ => "((),(" ++ inner ++ "),)") "Word"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) left
      let _ ← checked text caller expected
    for text in ["Unknown", "(Word,Unknown)", "(Unknown,())", "((Unknown),)", "((),(Word,Unknown))"] do
      let source ← parsed text
      assertTrue (interpretStructuralType? caller source).isNone "missing written leaf received a fallback or was skipped"
  let _ ← checked "(Pkg /* first */ . Flag, Word)" table (.product .bool .word)
  let _ ← checked "(PairAlias,())" table (.product (.product .word .bool) .unit)
  let _ ← checked "((),())" [] (.product .unit .unit)
  let singleton ← parsed "(Word,)"
  assertTrue (match singleton.value with
    | .tuple [⟨span, .named name none⟩] => decide (span.startByte = 1 ∧ span.endByte = 5 ∧ qualifiedTypeNameKey name = ["Word"])
    | _ => false) "type singleton was rewritten into expression grouping"
  let nested ← parsed "((Word,Bool),())"
  assertTrue (match nested.value with
    | .tuple [⟨leftSpan, .tuple [left, right]⟩, ⟨unitSpan, .tuple []⟩] =>
        nested.span.contains leftSpan && leftSpan.contains left.span && leftSpan.contains right.span &&
        nested.span.contains unitSpan && decide (left.span.endByte < right.span.startByte ∧ leftSpan.endByte < unitSpan.startByte)
    | _ => false) "original nested associations or child ranges changed"
  for text in ["(Word,Bool,Word)", "((),(),(),())", "Word<Bool>", "(Word<Bool>)",
      "mapping(Word => Bool)", "@Word", "function(Word) returns(Bool)", "comptime<Word>",
      "((),@Word)", "(function() returns(),Word)"] do
    let source ← parsed text
    assertTrue (interpretStructuralType? table source).isNone "unsupported written constructor gained meaning"
  let missing ← parsed "(Word,New)"
  assertTrue (interpretStructuralType? table missing).isNone "unknown structural child already accepted"
  let _ ← checked "(Word,New)" (table ++ [(["New"], .bool)]) (.product .word .bool)
  let known ← parsed "(Word,Bool)"
  assertTrue (decide (interpretStructuralType? ((["Word"], .unit) :: table) known = some (.product .unit .bool)))
    "first-match meaning-changing shadowing was ignored"
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    simp (config := { contextual := true }) [table, TypeNameTable.lookup?]
  for text in ["(Word,Bool)", "(Word,Unknown)", "()", "(Word,Bool,Word)"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table ++ table) sameLookup source
    assertTrue (decide (interpretStructuralType? table source = interpretStructuralType? (table ++ table) source))
      "duplicate-suffix lookup-equivalent tables changed the full optional result"
  oldGateRejected "function unitParam(x: ()){return ();}" [u] .unit
  oldGateRejected "function pairParam(x: (Word,Bool)){return ();}" [p] (.product .word .bool)
  oldGateRejected "function singleParam(x: (Word)) returns(Word){return x;}" [w] .word
  oldGateRejected "function unitReturn() returns(()){return ();}" [] .unit
  oldGateRejected "function pairReturn(x: Word,c: Bool) returns((Word,Bool)){return (x,c);}" [w,b] (.product .word .bool)
  oldGateRejected "function singleReturn(x: Word) returns((Word)){return x;}" [w] .word
  oldGateRejected "function unitLet(){let x: ()=();return x;}" [] .unit
  oldGateRejected "function pairLet(x: Word,c: Bool) returns(PairAlias){let p: (Word,Bool)=(x,c);return p;}" [w,b] (.product .word .bool)
  for text in ["", "(", "Word Bool", "(Word,,Bool)", "(Word,Bool))", "(,)", "Word<>"] do
    assertTrue (← parsed? text).isNone s!"incomplete or malformed type accepted: {text}"
end Tests
