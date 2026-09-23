import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation

/-! Two original rejection fixtures retain the exact Binary caller and source file.
Only the new recursive interpretation changes; old endpoints still reject them. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveNegatedComparisonMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)]
private def context : Resolved.Context := [(id 7,.word),(foreign,.function .word .word),(id 9,.function .word .word),(id 14,.word),(id 15,.bool),(foreign,.bool)]

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) :
    IO (Static table ctx s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match typed : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some t,some n =>
              have r : ResolvesLocalExpression table s (.var localId) := by
                rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named)
              have ty : Resolved.HasType ctx (.var localId) t := .var (Resolved.LocalScope.lookup?_iff.mp typed)
              return ⟨.var n,t,.pure r (.var (Resolved.LocalScope.index?_iff.mp indexed)) ty,.pure (r.reflects_type ty)⟩
          | _,_ => throw (IO.userError "original ordered context")
      | _ => throw (IO.userError "original names")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.binary left ⟨_,.notEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordEq a.core b.core),.bool,
        by rw [shape]; exact .notEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .notEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | ⟨_,.binary left ⟨_,.lessEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (.binary .wordGt a.core b.core),.bool,
        by rw [shape]; exact .lessEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .lessEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveNegatedComparisonMigrations
open ParsedRecursiveNegatedComparisonMigrations

def frontendParsedRecursiveNegatedComparisonMigrationTests : IO Unit := do
  for (text,op) in [("f(x) != g(y)",Core.BinaryOp.wordEq),("f(x) <= g(y)",.wordGt)] do
    let expected := Core.Expr.unary .boolNot (.binary op (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 3)))
    let file : Syntax.SourceFile := ⟨⟨.main,"recursive-binary.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
    let a ← statics names context s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=.bool ∧
      elaborateRecursiveLocalComputation? names context s=some (expected,.bool) ∧
      elaborateLocalExpression? names context s=none ∧
      elaborateLocalComputation? names context s=none)) "exact new comparison and unchanged old rejections"

end Tests
