import Solcore.Syntax.Parser.Signature
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeParameterDeclarationsPositionProperties
import Solcore.Frontend.RuntimeParametersPositionProperties
import Solcore.Frontend.RuntimeParameterDeclarationsTypeExtensionProperties
import Solcore.Frontend.RuntimeParameterDeclarationsOwnerProperties

/-! Complete original parameter lists have independent structural/declaration/binding
certificates. Expected rows and actual values are separate; products are never flattened. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedStructuralParameters
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 34⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 99 }
private def table : TypeNameTable := [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
  (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
  (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
private def w (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo n), .word⟩
private def b (v : Bool) : TypedRuntimeArgument := ⟨.bool, .bool v, .bool⟩
private def u : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def pair (left right : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product left.type right.type, .pair left.value right.value, .pair left.valueTyped right.valueTyped⟩
private def parsed? (content : String) : IO (Option (Syntax.DelimitedList Syntax.FunctionParameter)) := do
  let file : Syntax.SourceFile := ⟨⟨.main, "structural-parameters.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionParameters (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "whole parameter range changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parameter parser invariant")
private def parsed (content : String) : IO (Syntax.DelimitedList Syntax.FunctionParameter) := do
  let some source ← parsed? content | throw (IO.userError s!"complete parameters rejected: {content}")
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named leaf missing")
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.evidence⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let l ← meaning types left; let r ← meaning types right
      return ⟨.product l.type r.type, by rw [atSource]; exact .pair l.evidence r.evidence⟩
  | _ => throw (IO.userError "unsupported independent annotation")
termination_by sizeOf source
private structure Declaration (types : TypeNameTable) (initial : LocalTypeInputs)
    (parameters : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial parameters inputs
private def declaration (types : TypeNameTable) (initial : LocalTypeInputs)
    (parameters : List Syntax.FunctionParameter) : IO (Declaration types initial parameters) := do
  match atParams : parameters with
  | [] => return ⟨initial, by rw [atParams]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest =>
      let head ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declaration types (initial.bindFresh owner name.value head.type) rest
        return ⟨tail.inputs, by rw [atParams]; exact .cons head.evidence unused tail.evidence⟩
      else throw (IO.userError "independent declaration repeats a name")
  | _ => throw (IO.userError "unsupported independent parameter")
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (parameters : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial parameters arguments inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) : IO (Binding types initial parameters arguments) := do
  match atParams : parameters, atArgs : arguments with
  | [], [] => return ⟨initial, by rw [atParams, atArgs]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: args =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest args
          return ⟨tail.inputs, by rw [atParams, atArgs]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "independent binding repeats a name")
      else throw (IO.userError "independent actual type mismatch")
  | _, _ => throw (IO.userError "independent shape/arity mismatch")
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name,row.id,row.type)
private def shifted (id : Resolved.DeclarationId) : Resolved.DeclarationId :=
  { id with declarationIndex := id.declarationIndex + 11 }
private theorem injective : Function.Injective shifted := by
  intro a b same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases a; cases b; simp_all [shifted]
private def check (types : TypeNameTable) (content : String) (expected : List (String × Core.Ty))
    (arguments : Option (List TypedRuntimeArgument) := none) : IO Unit := do
  let source ← parsed content
  let original ← declaration types .empty source.elements
  let expectedRows := expected.zipIdx.map fun (row,index) => (row.1,(⟨owner,index⟩ : Resolved.LocalId),row.2)
  assertTrue (decide (rows original.inputs = expectedRows.reverse ∧ source.elements.length = expected.length ∧
    original.inputs.context.values = (expected.map Prod.snd).reverse)) "independent exact declaration/layout mismatch"
  have accepted := RuntimeParametersDeclare.complete original.evidence
  have _ := declareRuntimeParameters?_iff.mpr original.evidence
  assertTrue (decide ((declareRuntimeParameters? types owner source.elements).map rows = some expectedRows.reverse))
    "executable declaration differs from original certificate"
  have _ := (RuntimeParametersDeclare.rows original.evidence).arity
  have _ := original.evidence.generated_ids
  let mapped := RuntimeParametersDeclare.map_owner original.evidence shifted injective
  have _ := mapped.complete
  let extension : TypeNameTable.Extends types (types ++ [(["Word"], .unit)]) :=
    TypeNameTable.Extends.append_right types _
  have _ := declareRuntimeParameters?_some_of_extends extension accepted
  assertTrue (decide ((declareRuntimeParameters? (types ++ [(["Word"], .unit)]) owner source.elements).map rows =
    some expectedRows.reverse)) "later conflicting leaf changed original rows"
  for index in List.range source.elements.length do
    match atParameter : source.elements[index]? with
    | some ⟨span, .typed none name annotation⟩ =>
        have _ := RuntimeParametersDeclare.position original.evidence atParameter
        have _ := (RuntimeParametersDeclare.rows original.evidence).row_at atParameter
        let independent ← meaning types annotation
        have row : RuntimeParameterDeclarationRow types ⟨span, .typed none name annotation⟩
            { name := name.value, id := ⟨owner,index⟩, type := independent.type } := .typed independent.evidence
        have _ := row
        assertTrue (source.span.contains span && span.contains name.span && span.contains annotation.span &&
          decide (original.inputs.context.lookup? ⟨owner,index⟩ = some independent.type ∧
            Resolved.LocalScope.index? original.inputs.ids ⟨owner,index⟩ = some (source.elements.length - 1 - index)))
          "original span, type lookup or reversed Core index changed"
    | _ => throw (IO.userError "accepted original position missing")
  match arguments with
  | none => pure ()
  | some args =>
      let bound ← binding types .empty source.elements args
      have erased := bound.evidence.erase_values
      have _ := original.evidence.result_unique erased
      have _ := RuntimeParametersBind.complete bound.evidence
      if matching : args.map (·.type) = original.inputs.context.values.reverse then
        have _ := RuntimeParametersDeclare.bind_typed_arguments original.evidence args matching
      else throw (IO.userError "typed restoration requires all original argument types")
      assertTrue (decide (rows bound.inputs.toTypeInputs = expectedRows.reverse ∧
        bound.inputs.environment.values = args.reverse.map (·.value) ∧ args.length = expected.length ∧
        (bindRuntimeParameters? types owner source.elements args).map (fun i => (i.names,i.context,i.environment)) =
          some (bound.inputs.names,bound.inputs.context,bound.inputs.environment))) "erasure/order or actual binding changed"
      for index in List.range args.length do
        match atParameter : source.elements[index]?, atArgument : args[index]? with
        | some ⟨span, .typed none name annotation⟩, some argument =>
            have _ := RuntimeParametersBind.position bound.evidence atParameter atArgument
            let independent ← meaning types annotation
            if same : independent.type = argument.type then
              have row : RuntimeParameterRow types ⟨span, .typed none name annotation⟩ argument
                  ⟨name.value,⟨owner,index⟩,argument.type,argument.value,argument.valueTyped⟩ := .typed (same ▸ independent.evidence)
              have _ := row
            else throw (IO.userError "original paired annotation differs from actual value type")
        | _, _ => throw (IO.userError "paired position disappeared")
private def sparse : LocalInputs := ⟨[
  ⟨"old",⟨owner,7⟩,.word,(w 9).value,.word⟩, ⟨"old",⟨owner,2⟩,.bool,.bool false,.bool⟩,
  ⟨"foreign",⟨other,999⟩,.unit,.unit,.unit⟩], by decide⟩
private def checkSparse : IO Unit := do
  let source ← parsed "(p: (Word,Bool), unit: ())"
  let args := [pair (w 9) (b true),u]
  let declared ← declaration table sparse.toTypeInputs source.elements
  let bound ← binding table sparse source.elements args
  have _ := declared.evidence.rows
  have _ := declared.evidence.generated_ids
  have _ := declared.evidence.bindings_length
  have _ := bound.evidence.erase_values
  have _ := declared.evidence.result_unique bound.evidence.erase_values
  have _ := declared.evidence.extend_types (TypeNameTable.Extends.append_right table [(["Word"],.unit)])
  if matching : sparse.context.values.reverse ++ args.map (·.type) = declared.inputs.context.values.reverse then
    have _ := declared.evidence.bind_typed_arguments sparse rfl args matching
  else throw (IO.userError "general retained-prefix restoration type equation failed")
  assertTrue (decide (declared.inputs.ids = [⟨owner,9⟩,⟨owner,8⟩,⟨owner,7⟩,⟨owner,2⟩,⟨other,999⟩] ∧
    declared.inputs.names.map Prod.fst = ["unit","p","old","old","foreign"] ∧
    rows bound.inputs.toTypeInputs = rows declared.inputs ∧
    bound.inputs.environment.values = args.reverse.map (·.value) ++ sparse.environment.values))
    "mixed sparse allocation, duplicate initial names or untouched actual tail changed"
end ParsedStructuralParameters
open ParsedStructuralParameters

def frontendParsedStructuralParameterTests : IO Unit := do
  check table "()" [] (some [])
  for text in ["(x: ())", "(x: (()))", "(x: ((),))"] do check table text [("x",.unit)] (some [u])
  for text in ["(x: (Word))", "(x: (Word,))", "(x: ((Word,),))"] do check table text [("x",.word)] (some [w 9])
  for c in [false,true] do
    let p := pair (w 9) (b c)
    for text in ["(x: (Word,Bool))", "(x: (Word,Bool,),)", "(x: ((Word,),(Bool,)))"] do
      check table text [("x",p.type)] (some [p])
    check table "(a: (), p: (Word,Bool), z: Word)" [("a",.unit),("p",p.type),("z",.word)] (some [u,p,w 2])
    check table "(x: ((Word,Bool),()), y: (Word,(Bool,())))"
      [("x",(pair p u).type),("y",(pair (w 2) (pair (b c) u)).type)] (some [pair p u,pair (w 2) (pair (b c) u)])
  check table "(Unit: Unit, empty: ())" [("Unit",.word),("empty",.unit)] (some [w 9,u])
  check table "(flag: (Pkg /* qualified */ . Flag,Word))" [("flag",.product .bool .word)] (some [pair (b true) (w 2)])
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [(w 7).value],
    .closure (.cons .word .nil) (.var rfl)⟩
  check table "(opaque: (Cell,Fn))" [("opaque",(pair cell closure).type)] (some [pair cell closure])
  for type in [Core.Ty.namedData ⟨91⟩, .product (.namedData ⟨73⟩) (.cell .bool), .function .unit (.namedData ⟨4⟩)] do
    for depth in [0,1,3,6] do
      let annotation := (List.range depth).foldl (fun text _ => "((),(" ++ text ++ "))") "N"
      let expected := (List.range depth).foldl (fun inner _ => Core.Ty.product .unit inner) type
      check [(["N"],type)] ("(x: " ++ annotation ++ ")") [("x",expected)]
  checkSparse
  for (text,args) in [("(x: ())",[]), ("(x: ())",[w 9]), ("()",[u]),
      ("(x: (Word,Bool))",[w 9,b true]), ("(x: (Word,Bool))",[pair (b true) (w 9)]),
      ("(x: (Word,Bool))",[b true]), ("(x: ((Word,Bool),()))",[pair (w 9) (pair (b true) u)]),
      ("(u: (), w: Word)",[w 9,u]), ("(unused: (N,()))",[pair (w 9) u])] do
    let source ← parsed text
    assertTrue (declareRuntimeParameters? table owner source.elements).isSome "valid static annotation requires no actual value"
    have _ := bindRuntimeParameters?_eq_none_iff (types := table) (owner := owner) (params := source.elements) (args := args)
    assertTrue (bindRuntimeParameters? table owner source.elements args).isNone "missing, flattened or wrongly typed argument accepted"
  for text in ["(x: (), x: ())", "(x: (Word,Bool,Word))", "(x: ((),Unknown))", "(x: (Unknown,()))",
      "(x: Word<Bool>)", "(x: (Word,@Bool))", "(x: mapping(Word => Bool))",
      "(x: function(Word) returns(Bool))", "(comptime x: ())"] do
    let source ← parsed text
    have _ := declareRuntimeParameters?_eq_none_iff (types := table) (owner := owner) (params := source.elements)
    assertTrue (declareRuntimeParameters? table owner source.elements).isNone "unsupported written parameter gained a row"
    assertTrue (bindRuntimeParameters? table owner source.elements [u]).isNone "unsupported actual parameter accepted"
  let missing ← parsed "(x: (Word,New))"
  assertTrue (declareRuntimeParameters? table owner missing.elements).isNone "unknown leaf was already accepted"
  check (table ++ [(["New"],.bool)]) "(x: (Word,New))" [("x",.product .word .bool)] (some [pair (w 9) (b true)])
  let known ← parsed "(x: (Word,Bool))"
  assertTrue (decide ((declareRuntimeParameters? ((["Word"],.unit) :: table) owner known.elements).map
    (fun i => i.context.values) = some [.product .unit .bool])) "first-match override was treated as extension"
  have sameLookup (key : List String) : table.lookup? key = (table ++ table).lookup? key := by
    simp (config := { contextual := true }) [table, TypeNameTable.lookup?]
  have backward : TypeNameTable.Extends (table ++ table) table := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup]
    exact TypeNameTable.lookup?_iff.mpr found
  for text in ["(x: (Word,Bool))", "(x: ())", "(x: (Word,Unknown))", "(x: (Word,Bool,Word))"] do
    let source ← parsed text
    have same := declareRuntimeParameters?_eq_of_mutual_extends
      (TypeNameTable.Extends.append_right table table) backward owner source.elements
    have _ := congrArg (Option.map rows) same
    assertTrue (decide ((declareRuntimeParameters? table owner source.elements).map rows =
      (declareRuntimeParameters? (table ++ table) owner source.elements).map rows)) "mutual meaning equivalence lost Some or None"
  for text in ["", "(x)", "(x:)", "(x: ()) trailing", "(x: (Word,,Bool))", "(x: comptime<Word>)"] do
    assertTrue (← parsed? text).isNone "malformed/incomplete source fabricated an annotation"
end Tests
