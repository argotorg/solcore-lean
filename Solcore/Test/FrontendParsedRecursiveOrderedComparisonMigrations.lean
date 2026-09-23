import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation

/-! Original ordered-comparison rejections retain both earlier caller layouts,
source files and operator spans. Older endpoints still reject these sources. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveOrderedComparisonMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def names : LocalNameTable := [("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)]
private def context : Resolved.Context := [(id 7,.word),(foreign,.function .word .word),(id 9,.function .word .word),(id 14,.word),(id 15,.bool),(foreign,.bool)]

private def negatedOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"NegatedComparisons",by decide⟩],by decide⟩⟩,60⟩
private def nid (n : Nat) : Resolved.LocalId := ⟨negatedOwner,n⟩
private def nforeign : Resolved.LocalId := ⟨{negatedOwner with declarationIndex := 91},302⟩
private def negatedNames : LocalNameTable := [("x",nid 7),("y",nid 14),("c",nid 15),("d",nid 16),("f",nforeign),("g",nid 9),("p",nid 20),("maker",nid 25),("true",nid 90),("false",nid 91),("f",nid 88)]
private def negatedContext : Resolved.Context := [(nid 7,.word),(nid 14,.word),(nid 15,.bool),(nid 16,.bool),(nforeign,.function .word .word),(nid 9,.function .word .word),(nid 20,.function .bool .bool),(nid 25,.function .word (.function .word .word)),(nid 90,.bool),(nid 91,.bool),(nforeign,.bool)]

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
  | ⟨_,.binary left ⟨_,.less⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨a.core.wordLt b.core,.bool,
        by rw [shape]; exact .less (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .less (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | ⟨_,.binary left ⟨_,.greaterEqual⟩ right⟩ =>
      let a ← statics table ctx left; let b ← statics table ctx right
      if same : a.type=.word ∧ b.type=.word then return ⟨.unary .boolNot (a.core.wordLt b.core),.bool,
        by rw [shape]; exact .greaterEqual (same.1 ▸ a.elaboration) (same.2 ▸ b.elaboration),
        by rw [shape]; exact .greaterEqual (same.1 ▸ a.typing) (same.2 ▸ b.typing)⟩
      else throw (IO.userError "Word comparison children")
  | _ => throw (IO.userError "migration original shape")
termination_by sizeOf s

end ParsedRecursiveOrderedComparisonMigrations
open ParsedRecursiveOrderedComparisonMigrations

def frontendParsedRecursiveOrderedComparisonMigrationTests : IO Unit := do
  let apply (fn arg : Nat) := Core.Expr.apply (.var fn) (.var arg)
  for (table,ctx,path,left,right) in
      [(names,context,"recursive-binary.sol",apply 1 0,apply 2 3),
       (negatedNames,negatedContext,"recursive-negated-comparisons.sol",apply 4 0,apply 5 1)] do
    for (text,ge) in [("f(x) < g(y)",false),("f(x) >= g(y)",true)] do
      let comparison := Core.Expr.letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
      let expected := if ge then .unary .boolNot comparison else comparison
      let file : Syntax.SourceFile := ⟨⟨.main,path⟩,text⟩
      let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
      let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
      check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original parsed source"
      match s.value with
      | .binary lhs ⟨opSpan,op⟩ rhs =>
          check (decide (op=(if ge then .greaterEqual else .less) ∧ opSpan.source=file.id ∧
            opSpan.startByte=5 ∧ opSpan.endByte=(if ge then 7 else 6) ∧
            lhs.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤rhs.span.startByte)) "original operator bytes/order"
      | _ => throw (IO.userError "original binary root")
      let a ← statics table ctx s
      have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
      have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
      have _ := a.elaboration.core_hasType
      check (decide (a.core=expected ∧ a.type=.bool ∧
        elaborateRecursiveLocalComputation? table ctx s=some (expected,.bool) ∧
        elaborateLocalExpression? table ctx s=none ∧
        elaborateLocalComputation? table ctx s=none)) "original new ordered Core and unchanged old rejections"

end Tests
