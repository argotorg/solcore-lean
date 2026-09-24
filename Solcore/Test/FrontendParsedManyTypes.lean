import Solcore.Syntax.Parser.Signature
import Solcore.Frontend.StructuralType
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParameters

/-! Original flat lists retain every child and range. Independent structural and
parameter certificates are compared with external ordered types and supplied values. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedManyTypes
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Many", by decide⟩], by decide⟩⟩, 36⟩
private def table : TypeNameTable := [(["W"], .word), (["W"], .unit), (["B"], .bool),
  (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main, "many-types.sol"⟩, text⟩
private def parsed? (text : String) : IO (Option Syntax.TypeExpr) := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨(file text).id,0,text.utf8ByteSize⟩)) "complete original type range lost"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "type parser invariant")
private def parsed (text : String) : IO Syntax.TypeExpr := do
  let some source ← parsed? text | throw (IO.userError s!"complete type rejected: {text}")
  return source
private def ranges (source : Syntax.TypeExpr) : IO Unit := do
  match source with
  | ⟨span, .tuple elements⟩ =>
      for child in elements do
        assertTrue (span.contains child.span) "original inner type range escaped its parent"
      for (left,right) in elements.zip elements.tail do
        assertTrue (decide (left.span.endByte < right.span.startByte)) "written child order changed"
      for child in elements do ranges child
  | _ => pure ()
termination_by sizeOf source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named leaf missing")
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [original]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [original]; exact .single inner.evidence⟩
  | ⟨_, .tuple [left,right]⟩ =>
      let l ← meaning types left; let r ← meaning types right
      return ⟨.product l.type r.type, by rw [original]; exact .pair l.evidence r.evidence⟩
  | ⟨span, .tuple (first :: second :: third :: rest)⟩ =>
      let head ← meaning types first; let tail ← meaning types ⟨span, .tuple (second :: third :: rest)⟩
      return ⟨.product head.type tail.type, by rw [original]; exact .many head.evidence tail.evidence⟩
  | _ => throw (IO.userError "outside independent type profile")
termination_by sizeOf source
private def checked (types : TypeNameTable) (text : String) (arity : Nat) (expected : Core.Ty) : IO Syntax.TypeExpr := do
  let source ← parsed text
  assertTrue (match source.value with | .tuple elements => decide (elements.length = arity) | _ => false)
    "original flat element count was normalized or rewritten"
  ranges source
  let independent ← meaning types source
  assertTrue (decide (independent.type = expected ∧ interpretStructuralType? types source = some expected))
    "ordered right-associated fixture type changed"
  have _ := interpretStructuralType?_iff.mpr independent.evidence
  have _ := independent.evidence.type_unique (interpretStructuralType?_sound independent.evidence.complete)
  assertTrue (interpretTypeName? types source).isNone "old named-only adapter accepted a product list"
  let replacement : Syntax.SourceSpan := ⟨⟨.external "other", "raw"⟩,99,1⟩
  have _ := interpretStructuralType?_span types source replacement
  assertTrue (decide (interpretStructuralType? types { source with span := replacement } = some expected))
    "outer-span transport changed original nested meanings"
  have extension : TypeNameTable.Extends types (types ++ [(["W"],.bool)]) :=
    TypeNameTable.Extends.append_right types _
  have _ := independent.evidence.extend_types extension
  have _ := interpretStructuralType?_some_of_extends extension independent.evidence.complete
  assertTrue (decide (interpretStructuralType? (types ++ [(["W"],.bool)]) source = some expected))
    "later conflicting duplicate changed a written leaf"
  return source
private def parameters (text : String) : IO (Syntax.DelimitedList Syntax.FunctionParameter) := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "parameter lexer invariant")
  let .ok source next := Syntax.Parser.functionParameters (Syntax.Parser.State.initial (file text) lexed)
    | throw (IO.userError "complete original parameters rejected")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨(file text).id,0,text.utf8ByteSize⟩)) "parameter list was partial or reranged"
  return source
private structure Declaration (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declaration (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) :
    IO (Declaration types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let head ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declaration types (initial.bindFresh owner name.value head.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons head.evidence unused tail.evidence⟩
      else throw (IO.userError "original names repeat")
  | _ => throw (IO.userError "unsupported original parameter shape")
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Binding types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original,actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: tailArgs =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest tailArgs
          return ⟨tail.inputs, by rw [original,actual]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate parameter spelling")
      else throw (IO.userError "supplied actual differs from the independent annotation type")
  | _,_ => throw (IO.userError "one original parameter requires one actual argument")
private def rows (inputs : LocalTypeInputs) := inputs.bindings.map fun row => (row.name,row.id,row.type)
private def checkParameters (types : TypeNameTable) (text : String) (expected : List (String × Core.Ty))
    (arguments : Option (List TypedRuntimeArgument) := none) : IO Unit := do
  let source ← parameters text
  let independent ← declaration types .empty source.elements
  let expectedRows := expected.zipIdx.map fun (row,index) => (row.1,(⟨owner,index⟩ : Resolved.LocalId),row.2)
  assertTrue (decide (rows independent.inputs = expectedRows.reverse ∧ source.elements.length = expected.length ∧
    (declareRuntimeParameters? types owner source.elements).map rows = some expectedRows.reverse)) "exact original row/order changed"
  have _ := RuntimeParametersDeclare.complete independent.evidence
  for index in List.range source.elements.length do
    match original : source.elements[index]? with
    | some ⟨span,.typed none name annotation⟩ =>
        ranges annotation
        have _ := RuntimeParametersDeclare.position independent.evidence original
        assertTrue (source.span.contains span && span.contains name.span && span.contains annotation.span &&
          decide (Resolved.LocalScope.index? independent.inputs.ids ⟨owner,index⟩ = some (expected.length - 1 - index)))
          "original parameter ranges or reversed Core index changed"
    | _ => throw (IO.userError "original declared position disappeared")
  match arguments with
  | none => pure ()
  | some args =>
      let actual ← binding types .empty source.elements args
      have _ := independent.evidence.result_unique actual.evidence.erase_values
      if matching : args.map (·.type) = independent.inputs.context.values.reverse then
        have _ := RuntimeParametersDeclare.bind_typed_arguments independent.evidence args matching
      else throw (IO.userError "static restoration lost supplied actual types")
      have _ := RuntimeParametersBind.complete actual.evidence
      assertTrue (decide (rows actual.inputs.toTypeInputs = expectedRows.reverse ∧
        actual.inputs.environment.values = args.reverse.map (·.value) ∧ args.length = expected.length ∧
        (bindRuntimeParameters? types owner source.elements args).map (fun i => (i.names,i.context,i.environment)) =
          some (actual.inputs.names,actual.inputs.context,actual.inputs.environment))) "products were flattened or values reordered"
private def w : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo 9),.word⟩
private def b : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩
private def u : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pair (l r : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product l.type r.type,.pair l.value r.value,.pair l.valueTyped r.valueTyped⟩
end ParsedManyTypes
open ParsedManyTypes

def frontendParsedManyTypeTests : IO Unit := do
  for (text,arity,expected) in [("()",0,Core.Ty.unit),("(W,)",1,.word),("(W,B)",2,.product .word .bool),
      ("(W,B,())",3,.product .word (.product .bool .unit)), ("(W,B,(),W,)",4,.product .word (.product .bool (.product .unit .word))),
      ("((W,B),(),W)",3,.product (.product .word .bool) (.product .unit .word)),
      ("(W,(B,()),W)",3,.product .word (.product (.product .bool .unit) .word)),
      ("((),(),(),())",4,.product .unit (.product .unit (.product .unit .unit)))] do
    let _ ← checked table text arity expected
  let flat ← checked table "(W,B,())" 3 (.product .word (.product .bool .unit))
  assertTrue (match flat.value with
    | .tuple [⟨a,.named _ none⟩,⟨b,.named _ none⟩,⟨c,.tuple []⟩] =>
        decide ((a.startByte,a.endByte,b.startByte,b.endByte,c.startByte,c.endByte) = (1,2,3,4,5,7))
    | _ => false) "flat source list or exact child byte ranges changed"
  assertTrue (decide (interpretStructuralType? table flat ≠ some (.product (.product .word .bool) .unit) ∧
    interpretStructuralType? table flat ≠ some (.product .word (.product .bool (.product .unit .unit)))))
    "left association or an extra terminal Unit was introduced"
  let qualified ← checked table "(Pkg /* kept */ . Flag,W,())" 3 (.product .bool (.product .word .unit))
  assertTrue (match qualified.value with
    | .tuple (⟨_,.named name none⟩ :: _) => decide (qualifiedTypeNameKey name = ["Pkg","Flag"])
    | _ => false) "qualified component boundaries collapsed into a raw dotted key"
  let _ ← checked table "(Unit,(),Unit)" 3 (.product .word (.product .unit .word))
  for type in [Core.Ty.namedData ⟨91⟩,.cell .bool,.function .unit (.namedData ⟨7⟩)] do
    for depth in [0,1,3,7] do
      let text := (List.range depth).foldl (fun inner _ => "(()," ++ inner ++ ",B,)") "(N,)"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit (.product inner .bool)) type
      let types := [(["N"],type),(["B"],.bool)]
      let _ ← checked types text (if depth = 0 then 1 else 3) expected
      checkParameters types ("(packed: " ++ text ++ ")") [("packed",expected)]
  let triple := pair w (pair b u)
  checkParameters table "(packed: (W,B,()))" [("packed",triple.type)] (some [triple])
  checkParameters table "(first: (), packed: (W,B,(),W,), last: W)"
    [("first",.unit),("packed",(pair w (pair b (pair u w))).type),("last",.word)] (some [u,pair w (pair b (pair u w)),w])
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w.value],
    .closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArgument := pair cell (pair closure u)
  checkParameters table "(opaque: (Cell,Fn,()))" [("opaque",opaqueArgument.type)] (some [opaqueArgument])
  for args in [[u],[w,b,u],[pair (pair w b) u],[pair w (pair u b)],[],[triple,u]] do
    let source ← parameters "(packed: (W,B,()))"
    assertTrue (declareRuntimeParameters? table owner source.elements).isSome "valid static triple depended on actual inhabitants"
    assertTrue (bindRuntimeParameters? table owner source.elements args).isNone "wrong count, flattening, association or order accepted"
  for text in ["(Missing,W,B)","(W,Missing,B)","(W,B,Missing)","(W,B,(),Missing)","(W,(B,Missing,()),())",
      "(W,@B,())","(W,B<W>,())","(W,mapping(W => B),())","(W,function() returns(B),())"] do
    let source ← parsed text
    have _ := interpretStructuralType?_eq_none_iff (table := table) (source := source)
    assertTrue (interpretStructuralType? table source).isNone "a written unknown or unsupported child was skipped"
  let missing ← parsed "(W,New,B)"
  assertTrue (interpretStructuralType? table missing).isNone "one-way extension's old failure disappeared"
  let _ ← checked (table ++ [(["New"],.unit)]) "(W,New,B)" 3 (.product .word (.product .unit .bool))
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    cases result : table.lookup? key with
    | none =>
        symm
        apply TypeNameTable.lookup?_eq_none_iff.mpr
        simpa only [List.map_append, List.mem_append, not_or] using
          And.intro (TypeNameTable.lookup?_eq_none_iff.mp result)
            (TypeNameTable.lookup?_eq_none_iff.mp result)
    | some type =>
        exact (TypeNameTable.lookup?_iff.mpr
          (TypeNameTable.Extends.append_right table table
            (TypeNameTable.lookup?_iff.mp result))).symm
  have backward : TypeNameTable.Extends (table ++ table) table := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup]
    exact TypeNameTable.lookup?_iff.mpr found
  for text in ["(W,B,())","(W,New,B)","(W,@B,())"] do
    let source ← parsed text
    have _ := interpretStructuralType?_congr_lookup table (table ++ table) sameLookup source
    have _ := interpretStructuralType?_eq_of_mutual_extends (TypeNameTable.Extends.append_right table table) backward source
    assertTrue (decide (interpretStructuralType? table source = interpretStructuralType? (table ++ table) source))
      "unequal lookup-equivalent tables changed the entire optional result"
    let params ← parameters ("(x: " ++ text ++ ")")
    have _ := declareRuntimeParameters?_eq_of_mutual_extends (TypeNameTable.Extends.append_right table table) backward owner params.elements
    assertTrue (decide ((declareRuntimeParameters? table owner params.elements).map rows =
      (declareRuntimeParameters? (table ++ table) owner params.elements).map rows)) "full optional declaration was not preserved"
  assertTrue (decide (interpretStructuralType? ((["W"],.unit) :: table) flat = some (.product .unit (.product .bool .unit))))
    "first-match conflicting prefix was treated as semantic extension"
  for text in ["(W,B,,())","(W,B,()) trailing","(W,B,()","(,W,B)"] do
    assertTrue (← parsed? text).isNone "malformed source manufactured a structural type"
end Tests
