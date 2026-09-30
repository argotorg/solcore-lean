import Solcore.Syntax.Parser.Function
import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.Computation

/-! Original source typing is constructed before either existence theorem or
checker is used. The body certificates contain no Core terms or positional indices. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaTyping
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaTyping",by decide⟩],by decide⟩⟩,148⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs := ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,
  ⟨"c",foreign,.bool⟩,⟨"f",id 20,.function .word .word⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),
  (["C"],.cell (.function .word .word))]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-typing.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "complete original lambda and retained diagnostics"
      return source
  | .reject _ _ => throw (IO.userError "source rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation name")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let a ← meaning child; return ⟨a.type,by rw [shape]; exact .single a.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning left; let b ← meaning right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩ | .integer => some ⟨.integer⟩
  | .product a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.product p.down r.down⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | .sum a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.sum p.down r.down⟩
  | .cell a => do let p ← wellFormed a; return ⟨.cell p.down⟩
  | .namedData _ => none
private structure Header (source : Syntax.Expr) (a b : Core.Ty) where
  name : String
  body : Syntax.Block
  evidence : ExpectedUnaryLambdaHeaderDeclares types owner outer source (.function a b)
    ⟨outer.bindFresh owner name a,body,a,b⟩
private def header (source : Syntax.Expr) (a b : Core.Ty) : IO (Header source a b) := do
  match shape : source with
  | ⟨span,.lambda keyword ⟨ps,[parameter]⟩ returns body⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains parameter.span && span.contains body.span &&
        decide (keyword.endByte≤ps.startByte ∧ ps.endByte≤body.span.startByte)) "original header/body ranges and order"
      let ⟨name,parameterProof⟩ : Σ name,PLift (ExpectedLambdaParameterDeclares types owner outer parameter a (outer.bindFresh owner name a)) ←
        match pshape : parameter with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [pshape]; exact .inferred⟩⟩
        | ⟨_,.typed none name annotation⟩ => do
            let m ← meaning annotation
            if same : m.type=a then pure ⟨name.value,⟨by rw [pshape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "header domain mismatch")
        | _ => throw (IO.userError "header parameter shape")
      match present : returns with
      | none => return ⟨name,body,by rw [shape,present]; exact .lambda parameterProof.down .omitted⟩
      | some annotation =>
          let m ← meaning annotation
          if same : m.type=b then return ⟨name,body,by rw [shape,present]; exact .lambda parameterProof.down (.annotated (same ▸ m.evidence))⟩
          else throw (IO.userError "header codomain mismatch")
  | _ => throw (IO.userError "header source profile")
private structure Child (inputs : LocalTypeInputs) (source : Syntax.Expr) where
  type : Core.Ty
  evidence : RecursiveLocalComputationHasType inputs.names inputs.context source type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Child inputs source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
      | some i => match typed : inputs.context.lookup? i with
          | some t => return ⟨t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | none => throw (IO.userError "source typing row")
      | none => throw (IO.userError "source name")
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original expression group"
      let c ← child inputs inner; return ⟨c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨span,.call callee ⟨args,[argument]⟩⟩ =>
      check (span.contains callee.span && span.contains args && args.contains argument.span) "original call children"
      let f ← child inputs callee; let a ← child inputs argument
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "source argument type")
      | _ => throw (IO.userError "source callable type")
  | _ => throw (IO.userError "independent child typing profile")
termination_by sizeOf source
private structure Pattern (source : Syntax.Pattern) where
  tag : Option Core.Word
  evidence : WordMatchPatternClassifies source tag
private def pattern (source : Syntax.Pattern) : IO (Pattern source) := do
  match shape : source with
  | ⟨_,.wildcard _⟩ => return ⟨none,by rw [shape]; exact .wildcard rfl⟩
  | ⟨_,.literal literal⟩ =>
      if zero : literal.value=.decimal "0" then
        return ⟨some Core.Word.zero,by
          rw [shape]; refine .literal ⟨literal,rfl,?_⟩
          change NumericLiteralDenotes literal.value 0; rw [zero]
          exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩
      else throw (IO.userError "original fixture literal")
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span && decide (span.startByte<inner.span.startByte ∧ inner.span.endByte<span.endByte)) "original pattern group ranges"
      let c ← pattern inner; return ⟨c.tag,by rw [shape]; exact .group c.evidence⟩
  | _ => throw (IO.userError "original pattern profile")
termination_by sizeOf source
private structure Body (inputs : LocalTypeInputs) (source : Syntax.Block) where
  type : Core.Ty
  evidence : ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inputs source type
private def body (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Body inputs source) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some source)⟩]⟩ =>
      let c ← child inputs source; return ⟨c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let c ← body inputs ⟨span,statements⟩; return ⟨c.type,by rw [shape]; exact .block c.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      let c ← child inputs initializer
      let tail ← body (inputs.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : annotation with
      | none => return ⟨tail.type,by rw [shape,present]; exact .inferred c.evidence tail.evidence⟩
      | some original =>
          let m ← meaning original
          if same : m.type=c.type then return ⟨tail.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence tail.evidence⟩
          else throw (IO.userError "source binding annotation")
  | ⟨span,⟨_,.expression expr true⟩::rest⟩ =>
      let c ← child inputs expr; let tail ← body inputs ⟨span,rest⟩
      return ⟨tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← child inputs condition; let t ← body inputs yes; let f ← body inputs no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protects : ComputationNamesProtected (inputs.names.map Prod.fst) yes := by
            intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : c.type=.bool ∧ f.type=t.type then return ⟨t.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protects t.evidence (same.2 ▸ f.evidence)⟩
          else throw (IO.userError "source conditional types")
      | _ => throw (IO.userError "source explicit scope barrier")
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,last],none⟩⟩⟩]⟩ =>
      let c ← child inputs scrutinee
      let p ← pattern first.value.pattern; let q ← pattern last.value.pattern
      have firstSmaller : sizeOf first.value.body < sizeOf first := by rcases first with ⟨_,⟨_,_⟩⟩; simp; omega
      have lastSmaller : sizeOf last.value.body < sizeOf last := by rcases last with ⟨_,⟨_,_⟩⟩; simp; omega
      let t ← body inputs first.value.body; let f ← body inputs last.value.body
      if same : c.type=.word ∧ q.tag=none ∧ f.type=t.type then
        return ⟨t.type,by
          rw [shape]; refine .wordMatch c.evidence ?_ (.inl same.1) (.inr ⟨last,by simp,same.2.1 ▸ q.evidence⟩) ?_ (by simp)
          · intro arm member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl; exact ⟨_,p.evidence⟩; exact ⟨_,q.evidence⟩
          · intro arm member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl; exact t.evidence; exact same.2.2 ▸ f.evidence⟩
      else throw (IO.userError "source match coverage and all-arm typing")
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[],some fallback⟩⟩⟩]⟩ =>
      let c ← child inputs scrutinee; let t ← body inputs fallback
      return ⟨t.type,by rw [shape]; exact .wordMatch c.evidence (by simp) (.inr (by simp)) (.inl rfl) (by simp) (by simpa using t.evidence)⟩
  | _ => throw (IO.userError "independent source body typing profile")
termination_by sizeOf source
private def accepted (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  let inner := outer.bindFresh owner h.name a
  let original ← body inner h.body
  let some domain := wellFormed a | throw (IO.userError "source domain WF")
  let some codomain := wellFormed b | throw (IO.userError "source codomain WF")
  if same : original.type=b then
    have sourceTyped : ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner outer source (.function a b) :=
      .lambda h.evidence domain.down codomain.down (by
        change ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inner h.body b
        exact Eq.mp (congrArg (fun t => ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner inner h.body t) same) original.evidence)
    have elaborates := (expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp sourceTyped
    have checked := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp sourceTyped
    have reflected := (expectedComputationLambdaHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr elaborates
    have checkedBack := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr checked
    have present : (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)).isSome=true := by
      obtain ⟨core,found⟩ := checked; rw [found]; rfl
    have _ := reflected; have _ := checkedBack; have _ := present
    check (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)).isSome "only now consult the existing checker; no Core output was chosen"
    check (decide (inner.names=(h.name,id 32)::outer.names ∧ inner.context=(id 32,a)::outer.context)) "source identity shadowing retains all outer rows"
    check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "old recursive lambda admission unchanged"
  else throw (IO.userError "source body and expected codomain disagree")
private def rejected (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) (typedMismatch : Bool := false) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  if typedMismatch then
    let original ← body (outer.bindFresh owner h.name a) h.body
    check (decide (original.type≠b)) "independent source body typing can disagree with the valid header"
    have _ := original.evidence
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr h.evidence
  if absent : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=none then
    have notTyped : ¬ ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner outer source (.function a b) := by
      intro typed
      obtain ⟨core,found⟩ := (expectedComputationLambdaHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp typed
      rw [absent] at found; cases found
    have _ := notTyped
    check (declareExpectedUnaryLambdaHeader? types owner outer source (.function a b)).isSome "original header-only acceptance is weaker"
  else throw (IO.userError "unselected or unsupported source body was accepted")
private def wholeRejected : IO Unit := do
  let text := "function wrap() returns(function(A) returns(A)){return lam(x){return x;};}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "whole lexer")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (next.atEnd && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty) "original complete function"
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "source-only typing does not extend whole function admission"
  | .reject _ _ => throw (IO.userError "whole rejected")
  | .invariant _ => throw (IO.userError "whole parser invariant")
end ParsedExpectedLambdaTyping
open ParsedExpectedLambdaTyping
def frontendParsedExpectedLambdaTypingTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x,)->A{return saved;}"] do accepted text .word .word
  accepted "lam(x:B)->A{return saved;}" .bool .word
  accepted "lam(x:A)->A{let x:A=f(x);let x=x;if(c){{let saved=x;return saved;}}else{match(x){case (0){return saved;}case ((_)){return x;}}}}" .word .word
  accepted "lam(x){let x=f(x);let x=x;if(c){{let saved=x;return saved;}}else{match(x){case (0){return saved;}case ((_)){return x;}}}}" .word .word
  accepted "lam(x){f(x);match(x){case 0{return saved;}case _{return x;}}}" .word .word
  accepted "lam(x:B)->B{match(x){default{return x;}}}" .bool .bool
  accepted "lam(x:(A,B))->(A,B){return x;}" (.product .word .bool) (.product .word .bool)
  accepted "lam(x:C)->A{return saved;}" (.cell (.function .word .word)) .word
  accepted "lam(x:A)->(){return;}" .word .unit
  accepted "lam(comptime){return comptime;}" .word .word 1
  rejected "lam(x){return x;}" .word .bool 0 true
  rejected "lam(x:A)->A{return c;}" .word .word 0 true
  for text in ["lam(x){return Missing;}","lam(x){return lam(y){return y;};}",
      "lam(x){if(c){{return x;}}else{return Missing;}}",
      "lam(x){if(c){{return x;}}else{let y:Missing=x;return x;}}",
      "lam(x){if(c){let saved=x;return saved;}else{return saved;}}",
      "lam(x){match(x){case 0{return x;}}}",
      "lam(x){match(x){case 0{return x;}case _{return c;}}}",
      "lam(x){match(x){case _{return x;}default{return Missing;}}}"] do rejected text .word .word
  rejected "lam(x){let ;}" .word .word 1
  wholeRejected
end Tests
