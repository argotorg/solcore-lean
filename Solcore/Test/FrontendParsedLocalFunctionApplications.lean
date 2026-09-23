import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.Safety

/-! Original single-argument calls have independent child resolution, lowering
and typing. Nominal static contexts supply no values; this is not a runner or
an extension of the old pure expression or runtime-entry profiles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalFunctionApplications
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalCalls", by decide⟩], by decide⟩⟩, 43⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{ owner with declarationIndex := 99 },999⟩
private def names : LocalNameTable := [("f",id 7), ("c",foreign), ("x",id 2), ("g",id 1),
  ("y",id 3), ("unitFn",id 4), ("pairFn",id 5), ("manyFn",id 6),
  ("notFn",id 0), ("ghost",id 123), ("f",id 0)]
private def context (parameter result : Core.Ty) : Resolved.Context :=
  [(id 88,.unit), (id 7,.function parameter result), (foreign,.bool), (id 2,parameter),
    (id 1,.function parameter result), (id 3,parameter), (id 4,.function .unit result),
    (id 5,.function (.product parameter parameter) result),
    (id 6,.function (.product parameter (.product parameter parameter)) result),
    (id 0,.word), (id 7,.bool)]
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"local-function-applications.sol"⟩,content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      check (decide (source.span = ⟨file.id,0,content.utf8ByteSize⟩)) "complete original expression span changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "expression parser invariant")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"complete call fixture did not parse: {content}")
  return source
private structure Child (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def child (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Child ctx source) := do
  match atSource : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | none => throw (IO.userError "independent child name absent")
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _,_ => throw (IO.userError "independent child context row absent")
  | ⟨_,.group inner⟩ =>
      let a ← child ctx inner
      return ⟨a.resolved,a.core,a.type,by rw [atSource]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [atSource]; exact .unit,.unit,.unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← child ctx left; let b ← child ctx right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,first :: second :: third :: rest⟩⟩ =>
      let a ← child ctx first; let b ← child ctx ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [atSource]; exact .many a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← child ctx left; let b ← child ctx right
      if ta : a.type = .word then
        if tb : b.type = .word then
          return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
            by rw [atSource]; exact .subtract a.resolution b.resolution,
            .binary a.lowered b.lowered,.binary
              (show Resolved.HasType ctx a.resolved .word from ta ▸ a.typing)
              (show Resolved.HasType ctx b.resolved .word from tb ▸ b.typing)⟩
        else throw (IO.userError "right subtraction type mismatch")
      else throw (IO.userError "left subtraction type mismatch")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child ctx condition; let a ← child ctx yes; let b ← child ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
            by rw [atSource]; exact .conditional c.resolution a.resolution b.resolution,
            .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole conditional arms disagree")
      else throw (IO.userError "conditional guard is not Bool")
  | _ => throw (IO.userError "outside independent pure child certificate")
termination_by sizeOf source
private structure Application (ctx : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates names ctx source core type
  typing : LocalFunctionApplicationHasType names ctx source type
private def application (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Application ctx source) := do
  match atSource : source with
  | ⟨_,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argumentsSpan &&
        argumentsSpan.contains argument.span && decide (callee.span.endByte ≤ argumentsSpan.startByte ∧
          argumentsSpan.startByte < argument.span.startByte ∧ argument.span.endByte < argumentsSpan.endByte))
        "original call children, delimiter ranges or written order changed"
      let f ← child ctx callee; let a ← child ctx argument
      match atType : f.type with
      | .function parameter result =>
          if same : a.type = parameter then
            let ft : Resolved.HasType ctx f.resolved (.function parameter result) := atType ▸ f.typing
            let argumentTyped : Resolved.HasType ctx a.resolved parameter := same ▸ a.typing
            return ⟨.apply f.core a.core,result,
              by rw [atSource]; exact .call f.resolution f.lowered ft a.resolution a.lowered argumentTyped,
              by rw [atSource]; exact .call (f.resolution.reflects_type ft) (a.resolution.reflects_type argumentTyped)⟩
          else throw (IO.userError "original singleton argument type mismatch")
      | _ => throw (IO.userError "callee is not a known Function")
  | _ => throw (IO.userError "not exactly one original root argument")
private def accepted (parameter result : Core.Ty) (text : String) (expected : Core.Expr) : IO Unit := do
  let source ← parsed text
  let ctx := context parameter result
  let original ← application ctx source
  have accepted := original.evidence.complete
  have _ := original.evidence.hasType
  have _ := original.evidence.core_hasType
  have _ := original.typing.elaborates_exact
  have _ := localFunctionApplicationHasType_iff_elaborates.mp original.typing
  have _ := (elaborateLocalFunctionApplication?_sound accepted).result_unique original.evidence
  have _ := original.typing.type_unique original.evidence.hasType
  have _ := elaborateLocalFunctionApplication?_iff.mp accepted
  have _ := elaborateLocalFunctionApplication?_core_hasType accepted
  match atSource : source with
  | ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      have shaped : elaborateLocalFunctionApplication? names ctx
          ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ = some (original.core,original.type) := by
        simpa only [atSource] using accepted
      have _ := elaborateLocalFunctionApplication?_children.mp shaped
      pure ()
  | _ => throw (IO.userError "independently accepted source lost its root call")
  check (decide (original.core = expected ∧ original.type = result ∧
    elaborateLocalFunctionApplication? names ctx source = some (expected,result) ∧
    Core.infer? ctx.values expected = some result ∧ elaborateLocalExpression? names ctx source = none))
    s!"original exact Core/type changed or the old pure profile gained calls: {text}"
  let wrong := Core.Expr.letE .unit (expected.weakenAt 0)
  check (decide (Core.infer? ctx.values wrong = some result)) "wrong provenance was not independently equally typed"
  if different : wrong ≠ original.core then
    have _ : ¬ LocalFunctionApplicationElaborates names ctx source wrong original.type :=
      fun other => different (other.result_unique original.evidence).1
    pure ()
  else throw (IO.userError "wrong-Core comparison collapsed")
private def rejected (parameter result : Core.Ty) (text : String) : IO Unit := do
  let source ← parsed text
  let ctx := context parameter result
  have _ := elaborateLocalFunctionApplication?_eq_none_iff (table := names) (context := ctx) (source := source)
  check (decide (elaborateLocalFunctionApplication? names ctx source = none ∧
    elaborateLocalExpression? names ctx source = none)) s!"unsupported whole application accepted: {text}"
private def firstMatch : IO Unit := do
  let source ← parsed "f(x)"
  let ctx := context .word .bool
  let original ← application ctx source
  let wrong := Core.Expr.apply (.var 4) (.var 3)
  check (decide (names.lookup? "f" = some (id 7) ∧ ctx.lookup? (id 7) = some (.function .word .bool) ∧
    Resolved.LocalScope.index? ctx.ids (id 7) = some 1 ∧ original.core = .apply (.var 1) (.var 3) ∧
    Core.infer? ctx.values wrong = some .bool)) "duplicate first-match or sparse positional lowering changed"
  if different : wrong ≠ original.core then
    have _ : ¬ LocalFunctionApplicationElaborates names ctx source wrong original.type :=
      fun other => different (other.result_unique original.evidence).1
    pure ()
  else throw (IO.userError "different function identity lost exact provenance")
  check (decide (elaborateLocalFunctionApplication? (("f",id 0) :: names) ctx source = none ∧
    elaborateLocalFunctionApplication? names ((id 7,.word) :: ctx) source = none))
    "changed first-match name/type was ignored despite retaining all old rows"
end ParsedLocalFunctionApplications
open ParsedLocalFunctionApplications

def frontendParsedLocalFunctionApplicationTests : IO Unit := do
  for (parameter,result) in [(Core.Ty.word,.bool), (.unit,.word), (.bool,.function .word .word),
      (.namedData ⟨91⟩,.namedData ⟨92⟩), (.word,.namedData ⟨91⟩),
      (.namedData ⟨91⟩,.function (.namedData ⟨92⟩) (.namedData ⟨93⟩)),
      (.cell .word,.product .word .bool), (.function .word .word,.unit),
      (.product .word .bool,.cell .bool)] do
    for text in ["f(x)", "(f)(x)", "((f))(((x)))", "f /* call */ ( /* arg */ x )"] do
      accepted parameter result text (.apply (.var 1) (.var 3))
    accepted parameter result "(c ? f : g)(x)" (.apply (.ifE (.var 2) (.var 1) (.var 4)) (.var 3))
    accepted parameter result "f(c ? x : y)" (.apply (.var 1) (.ifE (.var 2) (.var 3) (.var 5)))
    accepted parameter result "(c ? (f) : g)(c ? x : (y))"
      (.apply (.ifE (.var 2) (.var 1) (.var 4)) (.ifE (.var 2) (.var 3) (.var 5)))
    accepted parameter result "unitFn(())" (.apply (.var 6) .unit)
    accepted parameter result "pairFn((x,y))" (.apply (.var 7) (.pair (.var 3) (.var 5)))
    accepted parameter result "manyFn((x,y,x))" (.apply (.var 8) (.pair (.var 3) (.pair (.var 5) (.var 3))))
  for count in [1,3,8,24] do
    let grouped := (List.range count).foldl (fun inner _ => "(" ++ inner ++ ")") "x"
    accepted .word .bool ("f(" ++ grouped ++ ")") (.apply (.var 1) (.var 3))
  accepted .word .bool "f(x - y)" (.apply (.var 1) (.binary .wordSub (.var 3) (.var 5)))
  firstMatch
  let spaced ← parsed "f /* call */ ( /* arg */ x )"
  match spaced.value with
  | .call callee ⟨span,[argument]⟩ =>
      check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 1 ∧
        span.startByte = "f /* call */ ".utf8ByteSize ∧
        argument.span.startByte = "f /* call */ ( /* arg */ ".utf8ByteSize ∧
        argument.span.endByte = "f /* call */ ( /* arg */ x".utf8ByteSize)) "exact original byte offsets were recreated"
  | _ => throw (IO.userError "original comment-separated argument changed shape")
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value,typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for text in ["f()", "f(x,y)", "f(x,y,x)", "pairFn(x,y)", "unitFn()", "unitFn(x)",
      "manyFn(((x,y),x))", "manyFn((x,y,x,()))", "notFn(x)", "x(x)", "f(c)",
      "missing(x)", "f(missing)", "ghost(x)", "f(ghost)", "(c ? f : missing)(x)",
      "(c ? f : notFn)(x)", "f((0 == 0) ? x : missing)", "f(c ? x : c)",
      "f(g(x))", "f(x)(y)", "(f(x))(y)", "(f(x))", "c ? f(x) : f(y)",
      "f.field(x)", "x.method(y)", "Pkg.f(x)", "f(x.field)",
      "(lam(z: Word){return z;})(x)", "f(lam(z: Word){return z;})"] do rejected .word .bool text
  for text in ["f(", "f(x", "f(x,)", "f(x,,y)", "f(x) trailing"] do
    check (← parsed? text).isNone "malformed or incomplete call acquired static meaning"
end Tests
