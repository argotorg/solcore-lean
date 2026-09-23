import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalExpressionTyping

/-! Exact old static function-annotation rejections become independent declarations.
Original files, owners, tables and source spelling stay fixed. Supplied Unit/Word
still fail binding; actual captured Boolean closures are separate positive inputs. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionParameters
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private structure Fixture where
  fileName : String
  owner : Resolved.DeclarationId
  table : TypeNameTable
  text : String
  returnStart : Nat
private def declarations : Fixture := {
  fileName := "parsed-parameter-declarations.sol"
  owner := ⟨⟨.main, ⟨[⟨"Declarations", by decide⟩], by decide⟩⟩, 2⟩
  table := [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Word"], .bool),
    (["Pkg", "Flag"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩),
    (["Pair"], .product .word .bool), (["Choice"], .sum .word .bool)]
  text := "(x: function(Word) returns (Bool))"
  returnStart := 27 }
private def parameters : Fixture := {
  fileName := "structural-parameters.sol"
  owner := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 34⟩
  table := [(["Word"], .word), (["Word"], .bool), (["Bool"], .bool),
    (["Unit"], .word), (["Pkg", "Flag"], .bool), (["Pkg.Flag"], .word),
    (["Cell"], .cell .word), (["Fn"], .function .word .word), (["N"], .namedData ⟨91⟩)]
  text := "(x: function(Word) returns(Bool))"
  returnStart := 26 }
private def parse {α : Type} (fixture : Fixture) (parser : Syntax.Parser.Parser α)
    (content : String) : IO α := do
  let file : Syntax.SourceFile := ⟨⟨.main, fixture.fileName⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := parser (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original source did not completely parse")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd)
    "original source lost complete diagnostic-free parsing"
  return source
private def range (fixture : Fixture) (start finish : Nat) : Syntax.SourceSpan :=
  ⟨⟨.main, fixture.fileName⟩, start, finish⟩
private def annotationMeaning (fixture : Fixture) (annotation : Syntax.TypeExpr) :
    IO (PLift (StructuralTypeDenotes fixture.table annotation (.function .word .bool))) := do
  match atAnnotation : annotation with
  | ⟨outer, .function keyword ⟨parameterSpan, [parameter]⟩ (some ⟨returnsSpan, [result]⟩)⟩ =>
      match atParameter : parameter, atResult : result with
      | ⟨wordSpan, .named wordName none⟩, ⟨boolSpan, .named boolName none⟩ =>
          assertTrue (decide (outer = range fixture 4 (fixture.text.utf8ByteSize - 1) ∧
            keyword = range fixture 4 12 ∧ parameterSpan = range fixture 12 18 ∧
            wordSpan = range fixture 13 17 ∧ returnsSpan = range fixture fixture.returnStart
              (fixture.returnStart + 6) ∧
            boolSpan = range fixture (fixture.returnStart + 1) (fixture.returnStart + 5) ∧
            qualifiedTypeNameKey wordName = ["Word"] ∧ qualifiedTypeNameKey boolName = ["Bool"]))
            "original keyword, delimiter, child range or name components changed"
          if leaves : fixture.table.lookup? (qualifiedTypeNameKey wordName) = some .word ∧
              fixture.table.lookup? (qualifiedTypeNameKey boolName) = some .bool then
            have first : StructuralTypeDenotes fixture.table parameter .word := by
              rw [atParameter]; exact .named (TypeNameTable.lookup?_iff.mp leaves.1)
            have second : StructuralTypeDenotes fixture.table result .bool := by
              rw [atResult]; exact .named (TypeNameTable.lookup?_iff.mp leaves.2)
            return ⟨by rw [atAnnotation]; exact .functionReturns first (.single second)⟩
          else throw (IO.userError "original first-match leaves changed")
      | _, _ => throw (IO.userError "original named leaves were replaced")
  | _ => throw (IO.userError "original unary/single-return type shape changed")
private def closure (flag : Bool) : TypedRuntimeArgument :=
  ⟨.function .word .bool, .closure .word .bool (.var 1) [.bool flag],
    .closure (.cons .bool .nil) (.var rfl)⟩
private def unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
private def word : TypedRuntimeArgument := ⟨.word, .word (Core.Word.ofNatModulo 9), .word⟩
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def check (fixture : Fixture) : IO Unit := do
  let source ← parse fixture Syntax.Parser.functionParameters fixture.text
  assertTrue (decide (source.span = range fixture 0 fixture.text.utf8ByteSize))
    "original whole parameter range changed"
  match atParameters : source.elements with
  | [⟨parameterSpan, .typed none name annotation⟩] =>
      let ⟨meaning⟩ ← annotationMeaning fixture annotation
      assertTrue (decide (name.value = "x" ∧ name.span = range fixture 1 2 ∧
        parameterSpan = range fixture 1 (fixture.text.utf8ByteSize - 1)))
        "original parameter spelling or range changed"
      let declared := LocalTypeInputs.empty.bindFresh fixture.owner name.value (.function .word .bool)
      have independent : RuntimeParametersDeclare fixture.table fixture.owner source.elements declared := by
        rw [atParameters]; exact .cons meaning (by simp) .nil
      have accepted := independent.complete
      have _ := declareRuntimeParameters?_iff.mpr independent
      have _ := independent.result_unique (declareRuntimeParameters?_sound accepted)
      have _ := RuntimeParametersDeclare.position independent (index := 0)
        (by rw [atParameters]; rfl)
      let expected := [("x", (⟨fixture.owner, 0⟩ : Resolved.LocalId), Core.Ty.function .word .bool)]
      assertTrue (decide (rows declared = expected ∧
        (declareRuntimeParameters? fixture.table fixture.owner source.elements).map rows = some expected ∧
        declared.context.values = [.function .word .bool] ∧
        declared.ids = [⟨fixture.owner, 0⟩])) "new annotation changed old exact static layout"
      assertTrue (interpretTypeName? fixture.table annotation).isNone
        "named-only interpretation silently acquired function syntax"
      let expression ← parse fixture Syntax.Parser.expression "x"
      match atExpression : expression with
      | ⟨_, .identifier occurrence⟩ =>
          if same : occurrence.value = name.value then
            have typing : LocalExpressionHasType declared.names declared.context expression (.function .word .bool) := by
              rw [atExpression]
              exact .identifier (by rw [same]; exact .head) .head
            have _ := localExpressionHasType_iff_elaborates.mp typing
          else throw (IO.userError "original reference spelling changed")
      | _ => throw (IO.userError "original identifier became another expression")
      assertTrue (decide (elaborateLocalExpression? declared.names declared.context expression =
        some (.var 0, .function .word .bool))) "original x reference changed Core index or type"
      let extra : TypeNameTable := [(["Word"], .unit), (["Fn"], .bool)]
      have extension : TypeNameTable.Extends fixture.table (fixture.table ++ extra) :=
        TypeNameTable.Extends.append_right fixture.table extra
      have _ := independent.extend_types extension
      have _ := declareRuntimeParameters?_some_of_extends extension accepted
      assertTrue (decide ((declareRuntimeParameters? (fixture.table ++ extra) fixture.owner source.elements).map rows =
        some expected)) "later duplicate changed the function domain or static rows"
      for flag in [false, true] do
        let argument := closure flag
        let bound := LocalInputs.empty.bindFresh fixture.owner name.value argument.type argument.value argument.valueTyped
        have binding : RuntimeParametersBind fixture.table fixture.owner source.elements [argument] bound := by
          rw [atParameters]; exact .cons meaning (by simp) .nil
        have erased := binding.erase_values
        have _ := independent.result_unique erased
        have _ := binding.complete
        have _ := RuntimeParametersBind.position binding (index := 0)
          (by rw [atParameters]; rfl) (by rfl)
        have _ := independent.bind_typed_arguments [argument] (by rfl)
        assertTrue (decide (rows bound.toTypeInputs = expected ∧
          bound.environment.values = [.closure .word .bool (.var 1) [.bool flag]] ∧
          (bindRuntimeParameters? fixture.table fixture.owner source.elements [argument]).map
            (fun inputs => (inputs.names, inputs.context, inputs.environment)) =
            some (bound.names, bound.context, bound.environment)))
          "binding lost the actual closure, its captured Boolean or original order"
      for arguments in [[unit], [word], [], [closure false, closure true]] do
        if rejected : bindRuntimeParameters? fixture.table fixture.owner source.elements arguments = none then
          have _ := bindRuntimeParameters?_eq_none_iff.mp rejected
          pure ()
        else throw (IO.userError "new static success bypassed old actual type/arity rejection")
  | _ => throw (IO.userError "original singleton runtime parameter changed")
end ParsedUnaryFunctionParameters

def frontendParsedUnaryFunctionParameterTests : IO Unit := do
  ParsedUnaryFunctionParameters.check ParsedUnaryFunctionParameters.declarations
  ParsedUnaryFunctionParameters.check ParsedUnaryFunctionParameters.parameters

end Tests
