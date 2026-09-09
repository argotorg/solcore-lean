import Solcore.Syntax.Parser.Function
import Solcore.Frontend.StructuralTypeTableProperties

/-! Complete original function annotations are certified independently of the
structural interpreter. Source parameter arity is never inferred from a packed type. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionTypes
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main,"structural-type.sol"⟩,content⟩
private def parsed? (content : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "type lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file content) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      check (decide (source.span=⟨(file content).id,0,content.utf8ByteSize⟩)) "whole original type range"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (content : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? content | throw (IO.userError s!"incomplete original type: {content}")
  return source
private structure Certificate (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes table source type
private def orderedChildren (outer : Syntax.SourceSpan) (children : List Syntax.TypeExpr) : Bool :=
  children.all (fun child => outer.contains child.span) &&
    (children.zip children.tail).all (fun adjacent => decide (adjacent.1.span.endByte≤adjacent.2.span.startByte))
private def certify (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Certificate table source) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : table.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original named leaf missing")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      check (source.span.contains child.span) "original singleton type range"
      let inner ← certify table child
      return ⟨inner.type,by rw [shape]; exact .single inner.meaning⟩
  | ⟨_,.tuple [left,right]⟩ =>
      check (orderedChildren source.span [left,right]) "original pair type order"
      let a ← certify table left; let b ← certify table right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.meaning b.meaning⟩
  | ⟨span,.tuple (first::second::third::rest)⟩ =>
      check (orderedChildren span (first::second::third::rest)) "all original tuple components"
      let head ← certify table first; let tail ← certify table ⟨span,.tuple (second::third::rest)⟩
      return ⟨.product head.type tail.type,by rw [shape]; exact .many head.meaning tail.meaning⟩
  | ⟨span,.function keyword ⟨parametersSpan,[parameter]⟩ returns⟩ =>
      check (span.contains keyword && span.contains parametersSpan && parametersSpan.contains parameter.span &&
        decide (keyword.endByte-keyword.startByte=8 ∧ keyword.endByte≤parametersSpan.startByte)) "original unary keyword and parameter list"
      let domain ← certify table parameter
      match present : returns with
      | none => return ⟨.function domain.type .unit,by rw [shape,present]; exact .functionDefault domain.meaning⟩
      | some ⟨returnsSpan,results⟩ =>
          check (span.contains returnsSpan && orderedChildren returnsSpan results &&
            decide (parametersSpan.endByte≤returnsSpan.startByte)) "original returns list and every written component"
          let codomain ← certify table ⟨returnsSpan,.tuple results⟩
          return ⟨.function domain.type codomain.type,by rw [shape,present]; exact .functionReturns domain.meaning codomain.meaning⟩
  | _ => throw (IO.userError "outside independent unary structural type profile")
termination_by sizeOf source
private def checked (content : String) (table : TypeNameTable) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed content
  let independent ← certify table source
  check (decide (independent.type=expected)) "independent original meaning versus literal expected type"
  have accepted := independent.meaning.complete
  have _ := interpretStructuralType?_iff.mpr independent.meaning
  have _ := independent.meaning.type_unique (interpretStructuralType?_sound accepted)
  check (decide (interpretStructuralType? table source=some expected)) "complete structural interpretation"
  check (interpretTypeName? table source).isNone "old named-only interpreter remains unchanged"
  let changed : Syntax.SourceSpan := ⟨⟨.external "unrelated","raw"⟩,92,1⟩
  have _ := interpretStructuralType?_span table source changed
  check (decide (interpretStructuralType? table {source with span:=changed}=some expected)) "outer range is not a semantic validity premise"
  let extras : TypeNameTable := [(["Word"],.unit),(["Unknown"],.bool)]
  have extension := independent.meaning.extend_types (TypeNameTable.Extends.append_right table extras)
  have _ := interpretStructuralType?_some_of_extends (TypeNameTable.Extends.append_right table extras) accepted
  check (decide (interpretStructuralType? (table++extras) source=some expected)) "later duplicates cannot override function children"
  have _ := extension.complete
  return source
-- This is the exact original standalone fixture table, not a new alias scheme.
private def table : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Unit"],.unit),
  (["PairAlias"],.product .word .bool),(["Pkg","Flag"],.bool),(["Pkg.Flag"],.word)]
private def rejected (content : String) (table : TypeNameTable) : IO Unit := do
  let source ← parsed content
  have _ := interpretStructuralType?_eq_none_iff (table := table) (source := source)
  check (interpretStructuralType? table source).isNone "unsupported arity or original child obtained a meaning"
  check (interpretTypeName? table source).isNone "old named-only rejection broadened"
end ParsedUnaryFunctionTypes
open ParsedUnaryFunctionTypes
def frontendParsedUnaryFunctionTypeTests : IO Unit := do
  let migrated ← checked "function(Word) returns(Bool)" table (.function .word .bool)
  check (match migrated.value with
    | .function keyword ⟨parametersSpan,[parameter]⟩ (some ⟨returnsSpan,[result]⟩) =>
        decide (keyword=⟨(file "").id,0,8⟩ ∧ parametersSpan=⟨(file "").id,8,14⟩ ∧
          parameter.span=⟨(file "").id,9,13⟩ ∧ returnsSpan=⟨(file "").id,22,28⟩ ∧ result.span=⟨(file "").id,23,27⟩) &&
          (match parameter.value,result.value with | .named a none,.named b none => decide (qualifiedTypeNameKey a=["Word"] ∧ qualifiedTypeNameKey b=["Bool"]) | _,_ => false)
    | _ => false) "exact old source shape, field spans and original table"
  for (A,B) in [(Core.Ty.word,Core.Ty.bool),(.namedData ⟨83⟩,.cell .word),(.function .unit .bool,.product .bool .unit)] do
    let caller : TypeNameTable := [(["Word"],A),(["Word"],.unit),(["Bool"],B)]
    let absent ← checked "function(Word)" caller (.function A .unit)
    let empty ← checked "function(Word) returns()" caller (.function A .unit)
    let explicitUnit ← checked "function(Word) returns(())" caller (.function A .unit)
    check (match absent.value,empty.value,explicitUnit.value with
      | .function _ _ none,.function _ _ (some ⟨_,[]⟩),.function _ _ (some ⟨_,[⟨_,.tuple []⟩]⟩) => true
      | _,_,_ => false) "equal Unit meanings do not erase original return presence or lists"
    for text in ["function(Word) returns(Bool)","function(Word,) returns(Bool,)","function((Word,)) returns((Bool,),)"] do
      let _ ← checked text caller (.function A B)
    let _ ← checked "function((Word,Bool)) returns(Word)" caller (.function (.product A B) A)
    let _ ← checked "function(()) returns(Bool)" caller (.function .unit B)
    let _ ← checked "function(Word) returns(Bool,Word,())" caller (.function A (.product B (.product A .unit)))
    let _ ← checked "function(Word) returns((Bool,Word),())" caller (.function A (.product (.product B A) .unit))
    let _ ← checked "function(function(Word) returns(Bool)) returns(function(Bool) returns(Word))" caller
      (.function (.function A B) (.function B A))
    for depth in [0,1,3,6] do
      let text := (List.range depth).foldl (fun inner _ => "function(Word) returns("++inner++")") "(Bool,())"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.function A inner) (.product B .unit)
      let _ ← checked text caller expected
    for count in [0,1,2,3,7] do
      let results := String.intercalate "," (List.replicate count "Bool")
      let expected := match count with
        | 0 => Core.Ty.unit
        | n+1 => (List.range n).foldl (fun inner _ => Core.Ty.product B inner) B
      let _ ← checked ("function(Word) returns("++results++")") caller (.function A expected)
    for text in ["function(Unknown)","function(Unknown) returns(Bool)","function(Word) returns(Unknown)",
        "function(Word) returns(Bool,Unknown)","function(Word) returns(Unknown,Bool)",
        "function(Word) returns(Bool,function(Unknown) returns(Bool))"] do rejected text caller
    for returns in [""," returns()"," returns(Bool)"," returns(Word,Bool)"] do
      rejected ("function()"++returns) caller
      rejected ("function(Word,Bool)"++returns) caller
      rejected ("function(Word,Bool,Word)"++returns) caller
  let _ ← checked "function(Pkg /* original */ . Flag) returns(PairAlias,())" table
    (.function .bool (.product (.product .word .bool) .unit))
  let _ ← checked "(function(()) returns(),function(Word) returns(Bool))" table
    (.product (.function .unit .unit) (.function .word .bool))
  for text in ["function() returns()","(function() returns(),Word)","(Word,function() returns(Bool),())",
      "function(Word<Bool>) returns(Bool)","function(@Word) returns(Bool)","function(comptime<Word>) returns(Bool)",
      "function(mapping(Word => Bool)) returns(Bool)","function(Word) returns(@Bool)",
      "function(Word) returns(Bool,mapping(Word => Bool))","function(Word) returns(function(Word,Bool))"] do rejected text table
  let unknown ← parsed "function(Word) returns(New)"
  check (interpretStructuralType? table unknown).isNone "unknown return starts rejected"
  let _ ← checked "function(Word) returns(New)" (table++[(["New"],.bool)]) (.function .word .bool)
  let _ ← checked "function(Word) returns(Bool)" ((["Word"],.unit)::table) (.function .unit .bool)
  have sameLookup (key : List String) : table.lookup? key=(table++table).lookup? key := by
    simp (config := {contextual := true}) [table,TypeNameTable.lookup?]
  for text in ["function(Word)","function(Word) returns(Bool)","function(Word) returns(Unknown)","function() returns(Bool)"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table++table) sameLookup source
    check (decide (interpretStructuralType? table source=interpretStructuralType? (table++table) source)) "whole Option agreement includes failures"
  for text in ["function(","function(Word) returns(","function(Word,,Bool)","function(Word) returns(Bool,,Word)","function(Word) Word"] do
    check (← parsed? text).isNone "incomplete or malformed original function type"
end Tests
