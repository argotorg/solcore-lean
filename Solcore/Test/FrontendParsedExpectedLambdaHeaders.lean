import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ExpectedUnaryLambdaHeader
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationFunctionCompilation
import Solcore.Frontend.ComputationFunctionEntry

/-! Original parsed headers are certified before the opt-in checker is used.
Separate inner-body evidence never becomes lambda admission or a runtime closure. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedLambdaHeaders
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaHeaders",by decide⟩],by decide⟩⟩,146⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs :=
  ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,⟨"x",foreign,.unit⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),(["B"],.word)]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-lambda-headers.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original full range and explicit recovery count"
      match source.value with
      | .lambda keyword parameters result body =>
          check (source.span.contains keyword && source.span.contains parameters.span && source.span.contains body.span &&
            decide (keyword.startByte=0 ∧ keyword.endByte=3 ∧ keyword.endByte≤parameters.span.startByte ∧ parameters.span.endByte≤body.span.startByte) &&
            parameters.elements.all (fun p => parameters.span.contains p.span && match p.value with
              | .inferred name => decide (p.span=name.span)
              | .typed marker name annotation => p.span.contains name.span && p.span.contains annotation.span &&
                  marker.toList.all (fun m => p.span.contains m && decide (m.endByte≤name.span.startByte))
              | .error => true) &&
            (result.toList.all fun r => source.span.contains r.span && decide (parameters.span.endByte≤r.span.startByte ∧ r.span.endByte≤body.span.startByte))) "original lambda fields and order"
      | _ => pure ()
      return source
  | .reject _ _ => throw (IO.userError "source rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (table : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes table source type
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Option (Meaning table source)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
      | none => return none
      | some type => return some ⟨type,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_,.tuple []⟩ => return some ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ =>
      let some m ← meaning table child | return none
      return some ⟨m.type,by rw [shape]; exact .single m.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let some a ← meaning table left | return none
      let some b ← meaning table right | return none
      return some ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ none⟩ =>
      let some a ← meaning table parameter | return none
      return some ⟨.function a.type .unit,by rw [shape]; exact .functionDefault a.evidence⟩
  | ⟨_,.function _ ⟨_,[parameter]⟩ (some ⟨span,results⟩)⟩ =>
      let some a ← meaning table parameter | return none
      let some b ← meaning table ⟨span,.tuple results⟩ | return none
      return some ⟨.function a.type b.type,by rw [shape]; exact .functionReturns a.evidence b.evidence⟩
  | _ => return none
termination_by sizeOf source
private structure Parameter (table : TypeNameTable) (p : Syntax.LambdaParameter) (a : Core.Ty) where
  name : String
  evidence : ExpectedLambdaParameterDeclares table owner outer p a (outer.bindFresh owner name a)
private def parameter (table : TypeNameTable) (p : Syntax.LambdaParameter) (a : Core.Ty) : IO (Option (Parameter table p a)) := do
  match shape : p with
  | ⟨_,.inferred name⟩ => return some ⟨name.value,by rw [shape]; exact .inferred⟩
  | ⟨_,.typed none name annotation⟩ =>
      let some m ← meaning table annotation | return none
      if same : m.type=a then return some ⟨name.value,by rw [shape]; exact .typed (same ▸ m.evidence)⟩
      else return none
  | _ => return none
private structure Header (table : TypeNameTable) (source : Syntax.Expr) (expected : Core.Ty) where
  output : DeclaredUnaryLambdaHeader
  evidence : ExpectedUnaryLambdaHeaderDeclares table owner outer source expected output
private def header (table : TypeNameTable) (source : Syntax.Expr) (expected : Core.Ty) : IO (Option (Header table source expected)) := do
  match shape : source, expectedShape : expected with
  | ⟨_,.lambda _ ⟨_,[p]⟩ result body⟩,.function a b =>
      let some declared ← parameter table p a | return none
      let output : DeclaredUnaryLambdaHeader := ⟨outer.bindFresh owner declared.name a,body,a,b⟩
      match present : result with
      | none => return some ⟨output,by rw [shape,present,expectedShape]; exact .lambda declared.evidence .omitted⟩
      | some annotation =>
          let some m ← meaning table annotation | return none
          if same : m.type=b then return some ⟨output,by rw [shape,present,expectedShape]; exact .lambda declared.evidence (.annotated (same ▸ m.evidence))⟩
          else return none
  | _,_ => return none
private structure Body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : ComputationReturnTreeElaborates RecursiveLocalComputationElaborates table owner inputs source core type
  typing : ComputationReturnTreeHasType RecursiveLocalComputationHasType table owner inputs source type
private def body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Option (Body table inputs source)) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return some ⟨.unit,.unit,by rw [shape]; exact .bare,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier name⟩)⟩]⟩ =>
      match named : inputs.names.lookup? name.value with
      | none => return none
      | some i => match typed : inputs.context.lookup? i, position : Resolved.LocalScope.index? inputs.context.ids i with
          | some t,some n => return some ⟨.var n,t,by
              rw [shape]; exact .expression (.pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp position)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))),by
              rw [shape]; exact .expression (.pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp typed)))⟩
          | _,_ => return none
  | _ => return none
private def accepted (text : String) (table : TypeNameTable) (a b : Core.Ty)
    (name : String := "x") (diagnostics : Nat := 0) (bodyExpected : Option (Core.Expr × Core.Ty) := none) : IO Unit := do
  let source ← parsed text diagnostics
  let some independent ← header table source (.function a b) | throw (IO.userError "independent original header")
  have complete := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
  match accepted : declareExpectedUnaryLambdaHeader? table owner outer source (.function a b) with
  | none => nomatch complete.symm.trans accepted
  | some output =>
      have restored := declareExpectedUnaryLambdaHeader?_iff.mp accepted
      have identical := independent.evidence.result_unique restored
      have provenance := independent.evidence.provenance_and_layout
      have notNone : declareExpectedUnaryLambdaHeader? table owner outer source (.function a b)≠none :=
        fun rejected => (declareExpectedUnaryLambdaHeader?_eq_none_iff.mp rejected) ⟨_,independent.evidence⟩
      have sameBody : output.body=independent.output.body := congrArg (·.body) identical.symm
      have _ := provenance; have _ := notNone
      check (decide (output.inputs.names=(name,id 32)::outer.names ∧ output.inputs.context=(id 32,a)::outer.context ∧
        output.parameterType=a ∧ output.returnType=b) && output.body==independent.output.body) "exact computed record, fresh owner-local row and original body"
      have _ := sameBody
      check (decide (outer.names.lookup? "x"=some (id 7) ∧ outer.context.lookup? (id 7)=some .bool ∧
        output.inputs.names.lookup? name=some (id 32))) "inner-first lookup retains old x and foreign sparse row"
      if let some expectedBody := bodyExpected then
        let some originalBody ← body table independent.output.inputs independent.output.body | throw (IO.userError "independent inner body")
        check (decide ((originalBody.core,originalBody.type)=expectedBody)) "literal body expectation independent of declared codomain"
        have checked := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr originalBody.evidence
        check (decide (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? table owner
          independent.output.inputs independent.output.body=some expectedBody)) "separate body checking only"
        have _ := checked; have _ := originalBody.typing
      check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "source lambda still excluded from recursive child"
private def rejected (text : String) (expected : Core.Ty) (diagnostics : Nat := 0) (table : TypeNameTable := types) : IO Unit := do
  let source ← parsed text diagnostics
  check (← header table source expected).isNone "independent header profile rejects"
  if rejected : declareExpectedUnaryLambdaHeader? table owner outer source expected=none then
    have noHeader := declareExpectedUnaryLambdaHeader?_eq_none_iff.mp rejected
    have _ := noHeader
  else throw (IO.userError "unsupported original header accepted")
private def bodyRejected (text : String) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  let some independent ← header types source (.function .word .bool) | throw (IO.userError "body-independent header")
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
  check (declareExpectedUnaryLambdaHeader? types owner outer source (.function .word .bool)).isSome "computed header accepts the unchanged bad body"
  check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "bad lambda body does not change the old child boundary"
  check (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types owner
    independent.output.inputs independent.output.body).isNone "valid header does not validate unresolved, ill-typed or recovered body"
private def wholeRejected (lambda : String) : IO Unit := do
  let text := "function outer() returns(function(A) returns(A)){return "++lambda++";}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "function lexer invariant")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
        decide (declaration.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original complete function"
      check (decide (interpretRuntimeFunctionHeader? types declaration.value.signature=some (.function .word .word)) &&
        (declareRuntimeParameters? types owner declaration.value.signature.parameters.elements).isSome) "named header and parameter policies already accept this original wrapper"
      match declaration.value.body.value with
      | [⟨_,.returnStmt (some source)⟩] =>
          let some independent ← header types source (.function .word .word) | throw (IO.userError "actual original returned lambda header")
          have _ := declareExpectedUnaryLambdaHeader?_iff.mpr independent.evidence
          check (declaration.value.body.span.contains source.span && (elaborateRecursiveLocalComputation? [] [] source).isNone) "actual returned source, not a fabricated lambda body"
      | _ => throw (IO.userError "original function body shape")
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old value-free compilation unchanged"
      check (prepareComputationFunction? elaborateRecursiveLocalComputation? types owner declaration []).isNone "old actual preparation unchanged"
      for fuel in [0,1,50] do
        check (runComputationFunction? elaborateRecursiveLocalComputation? types owner declaration [] fuel []).isNone "no source lambda runner admission"
  | .reject _ _ => throw (IO.userError "function rejected")
  | .invariant _ => throw (IO.userError "function parser invariant")
end ParsedExpectedLambdaHeaders
open ParsedExpectedLambdaHeaders
def frontendParsedExpectedLambdaHeaderTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x,){return x;}","lam(x:A){return x;}","lam(x)->A{return x;}",
      "lam(x:A)->A{return x;}","lam /* keyword */ ( x : (A,) , ) -> (A,) { return x; }"] do
    accepted text types .word .word "x" 0 (some (.var 0,.word))
  accepted "lam(x:A)->B{return x;}" types .word .bool "x" 0 (some (.var 0,.word))
  accepted "lam(x){return x;}" types .word .bool "x" 0 (some (.var 0,.word))
  accepted "lam(x){return;}" types .word .bool "x" 0 (some (.unit,.unit))
  accepted "lam(x){return x;}" types .word (.cell .word) "x" 0 (some (.var 0,.word))
  accepted "lam(x:A)->(){return;}" types .word .unit "x" 0 (some (.unit,.unit))
  accepted "lam(x:(A,B))->(A,B){return x;}" types (.product .word .bool) (.product .word .bool) "x" 0 (some (.var 0,.product .word .bool))
  accepted "lam(x:function(A) returns(B))->function(A) returns(B){return x;}" types (.function .word .bool) (.function .word .bool) "x" 0 (some (.var 0,.function .word .bool))
  accepted "lam(comptime){return comptime;}" types .word .word "comptime" 1 (some (.var 0,.word))
  accepted "lam(comptime:A)->A{return comptime;}" types .word .word "comptime" 1 (some (.var 0,.word))
  for text in ["lam(x){return Missing;}","lam(x){let x:B=saved;return x;}"] do bodyRejected text
  bodyRejected "lam(x){let ;}" 1
  for text in ["lam(){return x;}","lam(x,y){return x;}","lam(x:A,x:A){return x;}",
      "lam(comptime x:A){return x;}","lam(x:B){return x;}","lam(x:Missing){return x;}",
      "lam(x)->B{return x;}","lam(x)->Missing{return x;}","lam(x:@A){return x;}",
      "lam(x)->mapping(A => B){return x;}","lam(x:function(A,B)){return x;}","x"] do
    rejected text (.function .word .word)
  rejected "lam(comptime x){return x;}" (.function .word .word) 1
  for expected in [Core.Ty.unit,.word,.bool,.product .word .bool,.cell .word] do rejected "lam(x){return x;}" expected
  let front : TypeNameTable := (["A"],.bool)::types
  accepted "lam(x:A)->A{return x;}" front .bool .bool "x" 0 (some (.var 0,.bool))
  rejected "lam(x:A)->A{return x;}" (.function .word .word) 0 front
  accepted "lam(x:A)->A{return x;}" (types++[(["A"],.unit),(["New"],.unit)]) .word .word "x" 0 (some (.var 0,.word))
  for lambda in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x){return Missing;}"] do wholeRejected lambda
end Tests
