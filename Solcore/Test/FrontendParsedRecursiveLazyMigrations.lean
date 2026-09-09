import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.LocalComputation

/-! The three former recursive-lazy rejections retain their original source,
source file, names and ordered contexts, including foreign and duplicate rows. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveLazyMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (unary : Bool) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨if unary then "Unary" else "Binary",by split <;> decide⟩],by simp⟩⟩,if unary then 58 else 56⟩
private def id (unary : Bool) (n : Nat) : Resolved.LocalId := ⟨owner unary,n⟩
private def foreign (unary : Bool) : Resolved.LocalId :=
  ⟨{owner unary with declarationIndex := 91},302⟩
private def names (unary : Bool) : LocalNameTable :=
  if unary then [("x",id true 7),("y",id true 14),("c",id true 15),("d",id true 16),
    ("f",foreign true),("g",id true 9),("p",id true 20),("maker",id true 25),("f",id true 88)]
  else [("x",id false 7),("f",foreign false),("g",id false 9),("y",id false 14),("c",id false 15),("f",id false 88)]
private def context (unary : Bool) : Resolved.Context :=
  if unary then [(id true 7,.bool),(id true 14,.bool),(id true 15,.bool),(id true 16,.bool),
    (foreign true,.function .bool .bool),(id true 9,.function .bool .bool),(id true 20,.function .bool .bool),
    (id true 25,.function .bool (.function .bool .bool)),(foreign true,.bool)]
  else [(id false 7,.bool),(foreign false,.function .bool .bool),(id false 9,.function .bool .bool),
    (id false 14,.bool),(id false 15,.bool),(foreign false,.bool)]

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
  | ⟨_,.unary ⟨_,.logicalNot⟩ inner⟩ =>
      let a ← statics table ctx inner
      if same : a.type=.bool then return ⟨.unary .boolNot a.core,.bool,
        by rw [shape]; exact .logicalNot (same ▸ a.elaboration),by rw [shape]; exact .logicalNot (same ▸ a.typing)⟩
      else throw (IO.userError "Bool prefix")
  | ⟨_,.binary left ⟨_,.logicalAnd⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core b.core (.bool false),.bool,
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalAnd (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Bool conjunction")
  | ⟨_,.binary left ⟨_,.logicalOr⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.bool ∧ b.type=.bool then return ⟨.ifE a.core (.bool true) b.core,.bool,
        by rw [shape]; exact .logicalOr (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .logicalOr (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Bool disjunction")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveLazyMigrations
open ParsedRecursiveLazyMigrations

def frontendParsedRecursiveLazyMigrationTests : IO Unit := do
  for (unary,text,expected) in [
      (false,"f(x) && g(y)",Core.Expr.ifE (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 3)) (.bool false)),
      (false,"f(x) || g(y)",.ifE (.apply (.var 1) (.var 0)) (.bool true) (.apply (.var 2) (.var 3))),
      (true,"!(f(x) && c)",.unary .boolNot (.ifE (.apply (.var 4) (.var 0)) (.var 2) (.bool false)))] do
    let file : Syntax.SourceFile := ⟨⟨.main,if unary then "recursive-unary.sol" else "recursive-binary.sol"⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
    let a ← statics (names unary) (context unary) s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=.bool ∧
      elaborateRecursiveLocalComputation? (names unary) (context unary) s=some (expected,.bool) ∧
      elaborateLocalExpression? (names unary) (context unary) s=none ∧
      elaborateLocalComputation? (names unary) (context unary) s=none)) "exact new success and unchanged old rejections"

end Tests
