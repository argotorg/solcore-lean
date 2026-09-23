import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalComputation

/-! Six original tuple rejection fixtures retain their exact source, owner,
file and ordered caller rows. Independent typing/elaboration meets literal Core. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveTupleMigrations

private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def rows (owner : Resolved.DeclarationId) (variant : Nat) : LocalNameTable × Resolved.Context :=
  let id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
  let foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
  let wordFn := Core.Ty.function .word .word
  match variant with
  | 0 => ([("x",id 7),("f",foreign),("g",id 9),("maker",id 12),("y",id 14),("c",id 15),("p",id 20),("f",id 88)],
      [(id 7,.word),(foreign,wordFn),(id 9,wordFn),(id 12,.function .word wordFn),(id 14,.word),(id 15,.bool),
       (id 20,.function (.product .word .unit) .word),(foreign,.bool)])
  | 1 => ([("x",id 7),("f",foreign),("g",id 9),("y",id 14),("c",id 15),("f",id 88)],
      [(id 7,.word),(foreign,wordFn),(id 9,wordFn),(id 14,.word),(id 15,.bool),(foreign,.bool)])
  | _ =>
      let boolNames := if variant=3 then [("true",id 90),("false",id 91)] else []
      let boolTypes := if variant=3 then [(id 90,Core.Ty.bool),(id 91,.bool)] else []
      ([("x",id 7),("y",id 14),("c",id 15),("d",id 16),("f",foreign),("g",id 9),("p",id 20),("maker",id 25)]++boolNames++[("f",id 88)],
       [(id 7,.word),(id 14,.word),(id 15,.bool),(id 16,.bool),(foreign,wordFn),(id 9,wordFn),
        (id 20,.function .bool .bool),(id 25,.function .word wordFn)]++boolTypes++[(foreign,.bool)])

private structure Static (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates table ctx s core type
  typing : RecursiveLocalComputationHasType table ctx s type

private def statics (table : LocalNameTable) (ctx : Resolved.Context) (s : Syntax.Expr) : IO (Static table ctx s) := do
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
          | _,_ => throw (IO.userError "original typed/indexed row")
      | _ => throw (IO.userError "original first name")
  | ⟨_,.group inner⟩ =>
      let a ← statics table ctx inner
      return ⟨a.core,a.type,by rw [shape]; exact .group a.elaboration,by rw [shape]; exact .group a.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (decide (span=tupleSpan ∧ left.span.startByte=span.startByte+1 ∧ right.span.endByte+1=span.endByte ∧
        left.span.endByte<right.span.startByte) && span.contains left.span && span.contains right.span) "original ordered tuple ranges"
      let a ← statics table ctx left; let b ← statics table ctx right
      return ⟨.pair a.core b.core,.product a.type b.type,by rw [shape]; exact .pair a.elaboration b.elaboration,
        by rw [shape]; exact .pair a.typing b.typing⟩
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← statics table ctx fn; let a ← statics table ctx arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
            by rw [shape]; exact .application (ft ▸ f.typing) (same ▸ a.typing)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.unary ⟨_,.bitNot⟩ inner⟩ =>
      let a ← statics table ctx inner
      if word : a.type=.word then return ⟨.unary .wordNot a.core,.word,
        by rw [shape]; exact .bitNot (word ▸ a.elaboration),by rw [shape]; exact .bitNot (word ▸ a.typing)⟩
      else throw (IO.userError "Word complement")
  | ⟨_,.conditional guard _ yes _ no⟩ =>
      let g ← statics table ctx guard; let a ← statics table ctx yes; let b ← statics table ctx no
      if valid : g.type=.bool ∧ b.type=a.type then return ⟨.ifE g.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ g.elaboration) a.elaboration (valid.2 ▸ b.elaboration),
        by rw [shape]; exact .conditional (valid.1 ▸ g.typing) a.typing (valid.2 ▸ b.typing)⟩
      else throw (IO.userError "whole guard/branch typing")
  | _ => throw (IO.userError "original migration shape")
termination_by sizeOf s

end ParsedRecursiveTupleMigrations
open ParsedRecursiveTupleMigrations

def frontendParsedRecursiveTupleMigrationTests : IO Unit := do
  let call (f x : Nat) := Core.Expr.apply (.var f) (.var x)
  let fixtures : List (Resolved.DeclarationId × String × String × Nat × Core.Expr × Core.Expr) := [
    (⟨⟨.main,⟨[⟨"Recursive",by decide⟩],by decide⟩⟩,53⟩,"recursive-computation.sol","(g(x),x)",0,call 2 0,.var 0),
    (⟨⟨.main,⟨[⟨"Binary",by decide⟩],by decide⟩⟩,56⟩,"recursive-binary.sol","(f(x),y)",1,call 1 0,.var 3),
    (⟨⟨.main,⟨[⟨"Conditional",by decide⟩],by decide⟩⟩,57⟩,"recursive-conditional.sol","(c ? f(x) : y,y)",2,.ifE (.var 2) (call 4 0) (.var 1),.var 1),
    (⟨⟨.main,⟨[⟨"Unary",by decide⟩],by decide⟩⟩,58⟩,"recursive-unary.sol","(~f(x),y)",2,.unary .wordNot (call 4 0),.var 1),
    (⟨⟨.main,⟨[⟨"NegatedComparisons",by decide⟩],by decide⟩⟩,60⟩,"recursive-negated-comparisons.sol","(f(x),y)",3,call 4 0,.var 1),
    (⟨⟨.main,⟨[⟨"OrderedComparisons",by decide⟩],by decide⟩⟩,62⟩,"recursive-ordered-comparisons.sol","(f(x),y)",3,call 4 0,.var 1)]
  for (owner,path,text,variant,left,right) in fixtures do
    let (table,ctx) := rows owner variant
    let expected := Core.Expr.pair left right; let expectedType := Core.Ty.product .word .word
    let file : Syntax.SourceFile := ⟨⟨.main,path⟩,text⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "migration lexer")
    let .ok s next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens) | throw (IO.userError "migration parser")
    check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (s.span=⟨file.id,0,text.utf8ByteSize⟩)) "unchanged original source"
    let a ← statics table ctx s
    have _ := elaborateRecursiveLocalComputation?_iff.mpr a.elaboration
    have _ := recursiveLocalComputationHasType_iff_elaborates.mp a.typing
    have _ := a.elaboration.core_hasType
    check (decide (a.core=expected ∧ a.type=expectedType ∧
      elaborateRecursiveLocalComputation? table ctx s=some (expected,expectedType) ∧
      elaborateLocalExpression? table ctx s=none ∧ elaborateLocalComputation? table ctx s=none)) "original tuple exact success and old rejection"

end Tests
