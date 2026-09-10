import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ExpectedLambdaLetBodyTyping
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.ComputationFunctionCompilation

/-! Original source typing precedes elaboration/checking. The lambda sees the
pre-binder scope; its parameter and the tail binder reuse one fresh ID in disjoint scopes.
The parsed declaration supplies the original block, not a parameter-preparation claim. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaLetBodies
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaLet",by decide⟩],by decide⟩⟩,150⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def base : List LocalTypeBinding := [⟨"saved",id 31,.word⟩,⟨"x",id 20,.word⟩,
  ⟨"c",⟨{owner with declarationIndex:=900},700⟩,.bool⟩]
private def inputs (self : Option Core.Ty) : LocalTypeInputs :=
  match self with
  | none => ⟨base,by decide⟩
  | some t => ⟨⟨"f",id 7,t⟩::base,by change (id 7 :: base.map (fun b => b.id)).Nodup; decide⟩
private def functionType : Core.Ty := .function .word .word
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["F"],functionType),(["F"],.bool)]
private def parsed (statements : String) (returnsClosure : Bool := false) : IO Syntax.FunctionDecl := do
  let text := "function route(f:A,saved:A,x:A,c:B) returns(" ++ (if returnsClosure then "F" else "A") ++ "){" ++ statements ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-let.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && next.diagnostics.isEmpty &&
        decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original full source and body range"
      return source
  | .reject _ _ => throw (IO.userError "function parse rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation name")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let c ← meaning child; return ⟨c.type,by rw [shape]; exact .single c.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ (some ⟨span,results⟩)⟩ =>
      let a ← meaning parameter; let b ← meaning ⟨span,.tuple results⟩
      return ⟨.function a.type b.type,by rw [shape]; exact .functionReturns a.evidence b.evidence⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | _ => none
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  type : Core.Ty
  evidence : RecursiveLocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
      | some ident => match typed : i.context.lookup? ident with
          | some t => return ⟨t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found) (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | none => throw (IO.userError "source type row")
      | none => throw (IO.userError "source name")
  | ⟨_,.group original⟩ => let c ← child i original; return ⟨c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨_,.call original ⟨_,[arg]⟩⟩ =>
      let f ← child i original; let a ← child i arg
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "argument source type")
      | _ => throw (IO.userError "source callable type")
  | _ => throw (IO.userError "independent child profile")
termination_by sizeOf s
private structure Body (i : LocalTypeInputs) (s : Syntax.Block) where
  type : Core.Ty
  evidence : ComputationReturnTreeHasType RecursiveLocalComputationHasType types owner i s type
private def body (i : LocalTypeInputs) (s : Syntax.Block) : IO (Body i s) := do
  match shape : s with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some original)⟩]⟩ =>
      let c ← child i original; return ⟨c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let t ← body i ⟨span,statements⟩; return ⟨t.type,by rw [shape]; exact .block t.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some original)⟩::rest⟩ =>
      let c ← child i original
      let t ← body (i.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : annotation with
      | none => return ⟨t.type,by rw [shape,present]; exact .inferred c.evidence t.evidence⟩
      | some annotation =>
          let m ← meaning annotation
          if same : m.type=c.type then return ⟨t.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence t.evidence⟩
          else throw (IO.userError "source let type")
  | ⟨span,⟨_,.expression original true⟩::rest⟩ =>
      let c ← child i original; let t ← body i ⟨span,rest⟩
      return ⟨t.type,by rw [shape]; exact .discard c.evidence t.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let t ← body i yes; let f ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protects : ComputationNamesProtected (i.names.map Prod.fst) yes := by
            intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : c.type=.bool ∧ f.type=t.type then return ⟨t.type,by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protects t.evidence (same.2 ▸ f.evidence)⟩
          else throw (IO.userError "original branch types")
      | _ => throw (IO.userError "explicit source scope barrier")
  | _ => throw (IO.userError "independent body profile")
termination_by sizeOf s
private def lambdaTyped (i : LocalTypeInputs) (s : Syntax.Expr) (a b : Core.Ty) :
    IO (PLift (ExpectedComputationLambdaHasType RecursiveLocalComputationHasType types owner i s (.function a b))) := do
  match shape : s with
  | ⟨span,.lambda keyword ⟨ps,[parameter]⟩ returns original⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains parameter.span && span.contains original.span) "unchanged lambda header and body ranges"
      let ⟨name,parameterProof⟩ : Σ name,PLift (ExpectedLambdaParameterDeclares types owner i parameter a (i.bindFresh owner name a)) ←
        match pshape : parameter with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [pshape]; exact .inferred⟩⟩
        | ⟨_,.typed none name annotation⟩ => do
            let m ← meaning annotation
            if same : m.type=a then pure ⟨name.value,⟨by rw [pshape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "lambda domain annotation")
        | _ => throw (IO.userError "lambda parameter shape")
      let returnProof : PLift (ExpectedLambdaReturnDenotes types returns b) ← match present : returns with
        | none => pure ⟨by rw [present]; exact .omitted⟩
        | some annotation => do
            let m ← meaning annotation
            if same : m.type=b then pure ⟨by rw [present]; exact .annotated (same ▸ m.evidence)⟩
            else throw (IO.userError "lambda codomain annotation")
      let inner := i.bindFresh owner name a
      check (decide (inner.names=(name,Resolved.freshLocalId owner i.ids)::i.names ∧
        inner.context=(Resolved.freshLocalId owner i.ids,a)::i.context)) "parameter extends only its old-scope inputs"
      let t ← body inner original
      let some aw := wellFormed a | throw (IO.userError "domain guard")
      let some bw := wellFormed b | throw (IO.userError "codomain guard")
      if same : t.type=b then return ⟨by
        rw [shape]; exact .lambda (.lambda parameterProof.down returnProof.down) aw.down bw.down (same ▸ t.evidence)⟩
      else throw (IO.userError "original lambda body type")
  | _ => throw (IO.userError "original unary lambda head")
private structure Original (i : LocalTypeInputs) (s : Syntax.Block) where
  type : Core.Ty
  evidence : ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType types owner i s type
private def original (i : LocalTypeInputs) (s : Syntax.Block) : IO (Original i s) := do
  match shape : s with
  | ⟨span,⟨headSpan,.letDecl name (some annotation) (some init)⟩::rest⟩ =>
      check (span.contains headSpan && headSpan.contains annotation.span && headSpan.contains init.span &&
        decide (annotation.span.endByte≤init.span.startByte) && rest.all (fun stmt => span.contains stmt.span)) "exact original typed head and tail ranges"
      let m ← meaning annotation
      match mt : m.type with
      | .function a b =>
          let initializer ← lambdaTyped i init a b
          let tailInputs := i.bindFresh owner name.value (.function a b)
          let tail ← body tailInputs ⟨span,rest⟩
          check (decide (tailInputs.names=(name.value,Resolved.freshLocalId owner i.ids)::i.names ∧
            tailInputs.context=(Resolved.freshLocalId owner i.ids,.function a b)::i.context)) "tail does not inherit the initializer parameter row"
          return ⟨tail.type,by rw [shape]; exact .binding (mt ▸ m.evidence) initializer.down tail.evidence⟩
      | _ => throw (IO.userError "explicit expected function type")
  | _ => throw (IO.userError "original typed lambda-let head")
private def oldRejected (declaration : Syntax.FunctionDecl) (i : LocalTypeInputs) : IO Unit := do
  check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isNone "old shared checker sees the same complete original block"
  check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old function entry sees the same original declaration"
private def accepted (text : String) (self : Option Core.Ty) (expected : Core.Ty) : IO Unit := do
  let declaration ← parsed text (expected == functionType)
  let i := inputs self
  let typed ← original i declaration.value.body
  check (decide (typed.type=expected)) "independent source result type"
  have elaborates := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed.evidence
  have checked := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp typed.evidence
  have _ := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr elaborates
  have _ := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr checked
  have present : (elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner i declaration.value.body).isSome=true := by
    obtain ⟨core,found⟩ := checked; rw [found]; rfl
  have _ := present
  match found : elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner i declaration.value.body with
  | some result =>
      have evidence := (elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mp found
      have _ := (elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
      have _ := evidence.core_hasType (fun e => e.core_hasType)
      have _ := evidence.provenance
      check (decide (result.2=expected)) "checker result only after original source typing"
  | none => throw (IO.userError "source-typed body rejected")
  oldRejected declaration i
private def rejected (text : String) (self : Option Core.Ty) (ordinary : Bool := false) : IO Unit := do
  let declaration ← parsed text
  if ordinary then
    let typed ← body (inputs self) declaration.value.body
    have present : (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body).isSome=true := by
      obtain ⟨core,evidence⟩ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed.evidence
      rw [(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence]; rfl
    have _ := present
    check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body).isSome "well-typed ordinary nonlambda head stays in the old profile"
  if absent : elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? types owner (inputs self) declaration.value.body=none then
    have noElab := (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp absent
    have _ := (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mpr noElab
    have noTyping : ∀ type,¬ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType types owner (inputs self) declaration.value.body type := by
      intro type typed
      obtain ⟨core,evidence⟩ := (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp typed
      exact noElab ⟨core,type,evidence⟩
    have _ := noTyping
  else throw (IO.userError "outside opt-in profile accepted")
private def scopes : IO Unit := do
  let i := inputs (some .word)
  let inner := i.bindFresh owner "x" .word
  let tail := i.bindFresh owner "f" functionType
  check (decide (inner.names.lookup? "f"=some (id 7) ∧ inner.names.lookup? "x"=some (id 32) ∧
    tail.names.lookup? "f"=some (id 32) ∧ tail.names.lookup? "x"=some (id 20))) "same fresh 32 reused in separate scopes with different meanings"
  check (decide (inner.context.lookup? (id 7)=some .word ∧ tail.context.lookup? (id 32)=some functionType ∧
    types.lookup? ["F"]=some functionType)) "old self payload type and first-match alias retained"
end ParsedExpectedLambdaLetBodies
open ParsedExpectedLambdaLetBodies
def frontendParsedExpectedLambdaLetBodyTests : IO Unit := do
  scopes
  for text in ["let f:F=lam(x){return f;};return f(x);",
      "let f:F=lam(x:A)->A{return f;};return f(x);",
      "let f:F=lam(f){return f;};return f(x);",
      "let f:function(A) returns(A)=lam(x:A)->A{let x:A=x;return saved;};let y:A=f(x);let y=y;if(c){{let f=y;return f;}}else{return f(y);}",
      "let f:F=lam(x){return saved;};f(x);return f(x);"] do accepted text (some .word) .word
  accepted "let f:F=lam(x){return f;};return f;" (some .word) functionType
  accepted "let f:F=lam(x){return f(x);};return f(x);" (some functionType) .word
  accepted "let f:F=lam(x){return x;};return f(x);" none .word
  for self in [none,some .word,some .bool] do rejected "let f:F=lam(x){return f(x);};return f(x);" self
  rejected "let f:F=lam(x){return f;};return f(x);" none
  rejected "let f:A=x;return f;" (some .word) true
  for text in ["let f=lam(x){return x;};return f(x);","let f:F;return x;",
      "let f:Missing=lam(x){return x;};return f;","let f:A=lam(x){return x;};return f;",
      "let f:F=lam(){return saved;};return f(x);","let f:F=lam(x,y){return x;};return f(x);",
      "let f:F=lam(x:B){return saved;};return f(x);","let f:F=lam(x)->B{return c;};return f(x);",
      "let f:F=lam(x){return c;};return f(x);","let f:F=lam(x){return Missing;};return f(x);",
      "let f:F=lam(x){return x;};let g:F=lam(y){return y;};return f(x);",
      "let f:F=lam(x){return x;};if(c){{return f(x);}}else{return Missing;}",
      "let f:F=lam(x){return x;};if(c){let f=x;return f;}else{return f(x);}"] do rejected text (some .word)
end Tests
