import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.RuntimeParameterDeclarations

/-! Actual parameter bindings retain complete records across meaning-preserving
tables. Original parsed occurrences and caller values are never reconstructed
from an executable result; erasure alone cannot identify runtime bundles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeParameterTypeExtensions
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ActualTypes", by decide⟩], by decide⟩⟩, 42⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 99 }
private def base : TypeNameTable := [(["Word"],.word), (["Bool"],.bool), (["Cell"],.cell .word),
  (["Fn"],.function .word .word), (["N"],.namedData ⟨91⟩), (["Pkg","Flag"],.bool),
  (["Pkg.Flag"],.word), (["Word"],.bool)]
private def alternate : TypeNameTable := [(["Pkg.Flag"],.word), (["N"],.namedData ⟨91⟩),
  (["Fn"],.function .word .word), (["Cell"],.cell .word), (["Bool"],.bool), (["Word"],.word),
  (["Pkg","Flag"],.bool), (["N"],.unit), (["Word"],.unit)]
private def extras : TypeNameTable := [(["New"],.bool), (["Word"],.unit)]
private def extended := base ++ extras
private theorem sameLookup (key : List String) : base.lookup? key = alternate.lookup? key := by
  by_cases w : ["Word"] = key; · subst key; rfl
  by_cases b : ["Bool"] = key; · subst key; rfl
  by_cases c : ["Cell"] = key; · subst key; rfl
  by_cases f : ["Fn"] = key; · subst key; rfl
  by_cases n : ["N"] = key; · subst key; rfl
  by_cases q : ["Pkg","Flag"] = key; · subst key; rfl
  by_cases s : ["Pkg.Flag"] = key; · subst key; rfl
  simp [base, alternate, TypeNameTable.lookup?, w, b, c, f, n, q, s]
private theorem fromLookup {left right : TypeNameTable}
    (same : ∀ key, left.lookup? key = right.lookup? key) : TypeNameTable.Extends left right := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward : TypeNameTable.Extends base alternate := fromLookup sameLookup
private theorem backward : TypeNameTable.Extends alternate base := fromLookup fun key => (sameLookup key).symm
private theorem grows : TypeNameTable.Extends base extended := TypeNameTable.Extends.append_right base extras
private def w (n : Nat) : TypedRuntimeArgument := ⟨.word,.word (Core.Word.ofNatModulo n),.word⟩
private def b (v : Bool) : TypedRuntimeArgument := ⟨.bool,.bool v,.bool⟩
private def u : TypedRuntimeArgument := ⟨.unit,.unit,.unit⟩
private def pair (a z : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.product a.type z.type,.pair a.value z.value,.pair a.valueTyped z.valueTyped⟩
private def rowData (row : TypedLocalBinding) := (row.name,row.id,row.type,row.value)
private theorem rowData_injective : Function.Injective rowData := by
  rintro ⟨an,ai,aType,av,ap⟩ ⟨bn,bi,bType,bv,bp⟩ same
  simp only [rowData, Prod.mk.injEq] at same
  rcases same with ⟨rfl,rfl,rfl,rfl⟩; rfl
private abbrev bindingDecidableEq : DecidableEq TypedLocalBinding := fun a z =>
  decidable_of_iff (rowData a = rowData z) ⟨fun same => rowData_injective same, fun same => congrArg rowData same⟩
attribute [local instance] bindingDecidableEq
private abbrev inputsDecidableEq : DecidableEq LocalInputs := fun a z =>
  decidable_of_iff (a.bindings = z.bindings) ⟨by cases a; cases z; intro same; cases same; rfl,
    fun same => congrArg LocalInputs.bindings same⟩
attribute [local instance] inputsDecidableEq
private def parsed (parameters : String) : IO Syntax.FunctionDecl := do
  let content := "function original" ++ parameters ++ "{return;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"parameter-type-extensions.sol"⟩,content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"original declaration did not parse: {parameters}")
  let params := source.value.signature.parameters
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,content.utf8ByteSize⟩ ∧ params.span =
      ⟨file.id,"function original".utf8ByteSize,"function original".utf8ByteSize + parameters.utf8ByteSize⟩))
    "original whole declaration or exact parameter byte range changed"
  for parameter in params.elements do
    let .typed _ name annotation := parameter.value | throw (IO.userError "parameter lost its original annotation")
    assertTrue (params.span.contains parameter.span && parameter.span.contains name.span &&
      parameter.span.contains annotation.span && decide (name.span.endByte ≤ annotation.span.startByte))
      "original annotation/name ranges or order changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent named meaning absent")
  | ⟨_,.tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      let inner ← meaning types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning types left; let z ← meaning types right
      return ⟨.product a.type z.type, by rw [atSource]; exact .pair a.evidence z.evidence⟩
  | ⟨span,.tuple (first :: second :: third :: rest)⟩ =>
      let a ← meaning types first; let z ← meaning types ⟨span,.tuple (second :: third :: rest)⟩
      return ⟨.product a.type z.type, by rw [atSource]; exact .many a.evidence z.evidence⟩
  | _ => throw (IO.userError "unsupported independent annotation")
termination_by sizeOf source
private structure Binding (types : TypeNameTable) (initial : LocalInputs)
    (parameters : List Syntax.FunctionParameter) (arguments : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial parameters arguments inputs
private def binding (types : TypeNameTable) (initial : LocalInputs) (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) : IO (Binding types initial parameters arguments) := do
  match atParams : parameters, atArgs : arguments with
  | [],[] => return ⟨initial, by rw [atParams,atArgs]; exact .nil⟩
  | ⟨_,.typed none name annotation⟩ :: rest, argument :: args =>
      let head ← meaning types annotation
      if same : head.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← binding types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest args
          return ⟨tail.inputs, by rw [atParams,atArgs]; exact .cons (same ▸ head.evidence) unused tail.evidence⟩
        else throw (IO.userError "independent duplicate parameter")
      else throw (IO.userError "independent caller type mismatch")
  | _,_ => throw (IO.userError "independent arity or profile mismatch")
private def checkMutual (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO Unit := do
  let params := source.value.signature.parameters.elements
  have _ := bindRuntimeParameters?_eq_of_mutual_extends forward backward owner params args
  have _ := bindRuntimeParameters?_eq_of_mutual_extends backward forward owner params args
  assertTrue (decide (bindRuntimeParameters? base owner params args = bindRuntimeParameters? alternate owner params args))
    "mutual extension changed the full Option, including actual bindings"
private def accepted (text : String) (names : List String) (args : List TypedRuntimeArgument) : IO Unit := do
  let source ← parsed text
  let params := source.value.signature.parameters.elements
  let original ← binding base .empty params args
  let expected := (names.zip args).zipIdx.map fun ((name,arg),index) =>
    (name,(⟨owner,index⟩ : Resolved.LocalId),arg.type,arg.value)
  assertTrue (decide (params.length = names.length ∧ args.length = names.length ∧
    original.inputs.bindings.map rowData = expected.reverse ∧
    original.inputs.environment.values = (args.map (·.value)).reverse)) "source arity, fresh IDs or reverse-once actual rows changed"
  have originalSome := RuntimeParametersBind.complete original.evidence
  have _ := RuntimeParametersBind.extend_types original.evidence grows
  have _ := bindRuntimeParameters?_some_of_extends grows originalSome
  have _ := RuntimeParametersBind.erase_values original.evidence
  assertTrue (decide (bindRuntimeParameters? base owner params args = some original.inputs ∧
    bindRuntimeParameters? extended owner params args = some original.inputs ∧
    bindRuntimeParameters? alternate owner params args = some original.inputs)) "exact complete input record was not retained"
  checkMutual source args
private def rejected (text : String) (args : List TypedRuntimeArgument) : IO Unit := do
  let source ← parsed text
  let params := source.value.signature.parameters.elements
  have _ := bindRuntimeParameters?_eq_none_iff (types := base) (owner := owner) (params := params) (args := args)
  checkMutual source args
  assertTrue (decide (bindRuntimeParameters? base owner params args = none ∧
    bindRuntimeParameters? extended owner params args = none)) "invalid arity, type, spelling or profile acquired a binding"
private def sparse : LocalInputs := ⟨[
  ⟨"old",⟨owner,7⟩,.word,(w 9).value,.word⟩, ⟨"old",⟨owner,2⟩,.bool,.bool false,.bool⟩,
  ⟨"foreign",⟨other,999⟩,.unit,.unit,.unit⟩], by decide⟩
private def retained : IO Unit := do
  let source ← parsed "(p: (Word, Bool, ()), last: ())"
  let params := source.value.signature.parameters.elements
  let args := [pair (w 9) (pair (b true) u),u]
  let original ← binding base sparse params args
  let changed ← binding alternate sparse params args
  have transported := RuntimeParametersBindFrom.extend_types original.evidence forward
  have same := transported.result_unique changed.evidence
  have _ := RuntimeParametersBindFrom.extend_types changed.evidence backward
  assertTrue (decide (original.inputs = changed.inputs ∧ original.inputs.ids =
    [⟨owner,9⟩,⟨owner,8⟩,⟨owner,7⟩,⟨owner,2⟩,⟨other,999⟩] ∧
    original.inputs.names.map Prod.fst = ["last","p","old","old","foreign"] ∧
    original.inputs.environment.values = (args.map (·.value)).reverse ++ sparse.environment.values ∧
    original.inputs.bindings.drop 2 = sparse.bindings)) "arbitrary initial full rows or owner-local sparse allocation changed"
  have _ := same
private def boundaries : IO Unit := do
  let source ← parsed "(x: (Word, New, ()))"
  let params := source.value.signature.parameters.elements
  let args := [pair (w 9) (pair (b true) u)]
  let enabled ← binding extended .empty params args
  have _ := RuntimeParametersBind.complete enabled.evidence
  checkMutual source args
  assertTrue (decide (bindRuntimeParameters? base owner params args = none ∧
    bindRuntimeParameters? extended owner params args = some enabled.inputs ∧ enabled.inputs.ids = [⟨owner,0⟩]))
    "one-way extension did not enable the same original actual argument"
  let changed := (["Word"],Core.Ty.bool) :: base
  have notExtension : ¬ TypeNameTable.Extends base changed := by
    intro extension
    have found : TypeNameTable.Lookup base ["Word"] .word := .head
    have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
    simp [changed, TypeNameTable.lookup?] at impossible
  have _ := notExtension
  let known ← parsed "(x: Word)"
  let p := known.value.signature.parameters.elements
  let first ← binding base .empty p [w 9]
  let second ← binding base .empty p [w 2]
  assertTrue (decide (changed.tail = base ∧ bindRuntimeParameters? changed owner p [w 9] = none ∧
    first.inputs.names = second.inputs.names ∧ first.inputs.context = second.inputs.context ∧
    first.inputs.environment ≠ second.inputs.environment ∧ first.inputs ≠ second.inputs))
    "old rows or erased types incorrectly identified different actual records"
  let nominal ← parsed "(x: ((), N, N))"
  match atParams : nominal.value.signature.parameters.elements with
  | [⟨span,.typed none name annotation⟩] =>
      let head ← meaning base annotation
      if unused : name.value ∉ LocalTypeInputs.empty.names.map Prod.fst then
        let inputs := LocalTypeInputs.empty.bindFresh owner name.value head.type
        have declared : RuntimeParametersDeclare base owner [⟨span,.typed none name annotation⟩] inputs :=
          .cons head.evidence unused .nil
        have _ := declared.extend_types grows
        have originalAccepted : declareRuntimeParameters? base owner nominal.value.signature.parameters.elements = some inputs := by
          rw [atParams]; exact declared.complete
        have _ := originalAccepted
        assertTrue (decide (head.type = .product .unit (.product (.namedData ⟨91⟩) (.namedData ⟨91⟩)) ∧
          (declareRuntimeParameters? base owner nominal.value.signature.parameters.elements).map (fun i => (i.names,i.context)) =
            some (inputs.names,inputs.context)))
          "nominal static declaration required fabricated actual arguments"
      else throw (IO.userError "empty static inputs had a name")
      have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
        rintro ⟨value,typed⟩; cases typed with
        | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
      assertTrue (bindRuntimeParameters? base owner nominal.value.signature.parameters.elements [pair u (pair (w 9) (w 2))]).isNone
        "static nominal meaning fabricated an inhabitant"
  | _ => throw (IO.userError "nominal original parameter shape changed")
end ParsedRuntimeParameterTypeExtensions
open ParsedRuntimeParameterTypeExtensions

def frontendParsedRuntimeParameterTypeExtensionTests : IO Unit := do
  assertTrue (decide (base ≠ alternate ∧ base.lookup? ["Pkg","Flag"] = some .bool ∧
    base.lookup? ["Pkg.Flag"] = some .word)) "dictionary contrast became identical or flattened"
  accepted "()" [] []
  for text in ["(u: ())", "(u: (()))", "(u: ((),))"] do accepted text ["u"] [u]
  for text in ["(x: Word)", "(x: (Word))", "(x: ((Word,),))"] do accepted text ["x"] [w 9]
  for c in [false,true] do
    accepted "(p: (Word, Bool))" ["p"] [pair (w 9) (b c)]
    accepted "(p: (Word, Bool, ()))" ["p"] [pair (w 9) (pair (b c) u)]
    accepted "(p: (Word, Bool, (), Word))" ["p"] [pair (w 9) (pair (b c) (pair u (w 2)))]
    accepted "(p: ((Word, Bool), ()))" ["p"] [pair (pair (w 9) (b c)) u]
    accepted "(u: (), p: (Word, Bool, ()), z: Word)" ["u","p","z"] [u,pair (w 9) (pair (b c) u),w 2]
    accepted "(q: (Pkg /* components */ . Flag, Word))" ["q"] [pair (b c) (w 2)]
  for count in [1,3,8,24] do
    let names := (List.range count).map fun n => s!"a{n}"
    accepted ("(" ++ String.intercalate "," (names.map (· ++ ": Word")) ++ ")") names ((List.range count).map w)
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 999,.cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [(w 7).value],
    .closure (.cons .word .nil) (.var rfl)⟩
  accepted "(c: Cell, f: Fn, p: ((),Cell,Fn))" ["c","f","p"] [cell,closure,pair u (pair cell closure)]
  retained; boundaries
  for (text,args) in [("()",[u]), ("(u: ())",[]), ("(u: ())",[w 9]),
      ("(p: (Word,Bool))",[w 9,b true]), ("(p: (Word,Bool))",[pair (b true) (w 9)]),
      ("(p: (Word,Bool,()))",[pair (pair (w 9) (b true)) u]),
      ("(p: (Word,Bool,()))",[pair (w 9) (pair (b true) (pair u u))]),
      ("(u: (),w: Word)",[w 9,u]), ("(x: Word,x: Word)",[w 9,w 2]),
      ("(x: Word<Bool>)",[w 9]), ("(comptime x: Word)",[w 9]),
      ("(x: mapping(Word => Bool))",[w 9]), ("(x: function(Word) returns(Bool))",[w 9]),
      ("(x: (Word,@Bool))",[pair (w 9) (b true)]),
      ("(x: (Unknown,Word))",[pair (w 9) (w 2)]), ("(x: (Word,Unknown))",[pair (w 9) (w 2)])] do
    rejected text args
end Tests
