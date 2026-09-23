import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TypedLetReturnTree

/-! The original complete declaration and actual arguments remain fixed while only
first-match type meanings change. Exact records, paths and saved states are retained. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RuntimeTypeExtensionEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeTypeExtensionEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "runtime-type-extension-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) s!"original complete ranges changed: {content}"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent type leaf missing")
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [atSource]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation grammar")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def parameters (types : TypeNameTable) (initial : LocalInputs)
    (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types initial params args) := do
  match atParams : params, atArgs : args with
  | [], [] => return ⟨initial, by rw [atParams, atArgs]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest, argument :: tailArgs =>
      check (span.contains name.span && span.contains annotation.span) "original parameter range changed"
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← parameters types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest tailArgs
          return ⟨tail.inputs, by rw [atParams, atArgs]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "original actual type mismatch")
  | _, _ => throw (IO.userError "unsupported parameter or argument count")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "independent context row missing")
      | none => throw (IO.userError "independent name missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | _ => throw (IO.userError "outside independent expression grammar")
termination_by sizeOf source
private structure Body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : TypedLetReturnTreeElaborates types owner s source core type
private def body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) : IO (Body types s source) := do
  match atSource : source with
  | ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ =>
      let a ← expression s returned
      return ⟨a.core, a.type, by rw [atSource]; exact .single (.expression a.resolution
        (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing)⟩
  | ⟨_, [⟨innerSpan, .block statements⟩]⟩ =>
      let child ← body types s ⟨innerSpan, statements⟩
      return ⟨child.core, child.type, by rw [atSource]; exact .block child.evidence⟩
  | ⟨span, ⟨ls, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original initializer spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        match atAnnotation : annotation with
        | none => return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
        | some written =>
            let m ← meaning types written
            if same : m.type = a.type then
              return ⟨.letE a.core b.core, b.type, by rw [atSource, atAnnotation]; exact .binding (same ▸ m.evidence) unused a.resolution a.lowered a.typing b.evidence⟩
            else throw (IO.userError "written annotation disagreed")
      else throw (IO.userError "ancestor name reused")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s source; let b ← body types s ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type,
        by rw [atSource]; exact .discard a.resolution a.lowered a.typing b.evidence⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s guard; let a ← body types s yes; let b ← body types s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.core a.core b.core, a.type, by rw [atSource]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.evidence (bt ▸ b.evidence)⟩
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent body grammar")
termination_by sizeOf source
private structure Preparation (types : TypeNameTable) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  prepared : PreparedRuntimeFunction
  evidence : RuntimeFunctionPrepares types owner source args prepared
private def prepare (types : TypeNameTable) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) :
    IO (Preparation types source args) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let b ← body types ps.inputs.toTypeInputs source.value.body
  match atClause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [returned]⟩⟩ =>
      let m ← meaning types returned
      if same : m.type = b.type then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨ps.inputs, b.core, b.type⟩, ⟨⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [atClause]; exact .single (same ▸ m.evidence)⟩, ps.evidence, b.evidence⟩⟩
        else throw (IO.userError "header policy rejected")
      else throw (IO.userError "return contract differs")
  | _ => throw (IO.userError "return clause is not singleton")

private def mixed : Core.Expr := .letE (.var 2) (.letE (.var 3) (.ifE (.var 2)
  (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1))))
private theorem mixedPaths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 17 else 13) ⟨.eval mixed [.bool c, y, x], k, store⟩ ⟨.ret x, k, store⟩ := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet
        (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))))

private def alternate (type : Core.Ty) : TypeNameTable := ((["T"], type) :: table type) ++ [(["T"], .unit)]
private def enlarged (type : Core.Ty) : TypeNameTable := table type ++ [(["Alias"], type)]
private theorem sameLookup (type : Core.Ty) (key : List String) : (table type).lookup? key = (alternate type).lookup? key := by
  by_cases t : ["T"] = key
  · subst key; rfl
  by_cases b : ["Bool"] = key
  · subst key; rfl
  simp [table, alternate, TypeNameTable.lookup?, t, b]
private theorem fromLookup {old next : TypeNameTable}
    (same : ∀ key, old.lookup? key = next.lookup? key) : TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))
private theorem forward (type : Core.Ty) : TypeNameTable.Extends (table type) (alternate type) := fromLookup (sameLookup type)
private theorem backward (type : Core.Ty) : TypeNameTable.Extends (alternate type) (table type) := fromLookup (fun key => (sameLookup type key).symm)
private def rows (inputs : LocalInputs) := inputs.bindings.map fun b => (b.name, b.id, b.type, b.value)
private def payload (p : PreparedRuntimeFunction) := (rows p.inputs, p.core, p.returnType)
private def text (body : String) := "function f(x:T,y:T,c:Bool) returns(T){" ++ body ++ "}"
private def mixedText (annotated : Bool) : String :=
  "{x;{let z" ++ (if annotated then ":T" else "") ++ "=x;{if(c){{(z,y);{return z;}}}else{{y;{return z;}}}}}}"
private def verify (old next : TypeNameTable) (extension : TypeNameTable.Extends old next)
    (content : String) (x y : TypedRuntimeArgument) (c : Bool) (expectedCore : Core.Expr) (cost : Nat)
    (paths : ∀ store k, Core.Steps cost ⟨.eval expectedCore [.bool c, y.value, x.value], k, store⟩ ⟨.ret x.value, k, store⟩) : IO Unit := do
  let source ← parsed content
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  let original ← prepare old source args
  let prepared := original.prepared
  check (decide (prepared.core = expectedCore ∧ prepared.returnType = x.type ∧ rows prepared.inputs =
    [("c", ⟨owner, 2⟩, .bool, .bool c), ("y", ⟨owner, 1⟩, y.type, y.value), ("x", ⟨owner, 0⟩, x.type, x.value)]))
    "independent complete record or one reversal changed"
  have _ := RuntimeParametersBindFrom.extend_types original.evidence.parameters extension
  have _ := RuntimeParametersBind.extend_types original.evidence.parameters extension
  have _ := bindRuntimeParameters?_some_of_extends extension original.evidence.parameters.complete
  have _ := original.evidence.extend_types extension
  have _ := original.evidence.hasType.extend_types extension
  have preserved := prepareRuntimeFunction?_some_of_extends extension original.evidence.complete
  match atNext : prepareRuntimeFunction? next owner source args with
  | none => throw (IO.userError "successful full preparation lost")
  | some result =>
      have _ : result = prepared := Option.some.inj (atNext.symm.trans preserved)
      check (decide (payload result = payload prepared)) "actual prepared record was replaced by a static projection"
  check (decide ((prepareRuntimeFunction? old owner source args).map payload = some (payload prepared)))
    "independent original preparation disagreed with executable preparation"
  for store in [[], [w 91, .cellRef .word 999]] do
    have _ := paths store [.unaryApply .wordNot]
    let start := Core.State.initial expectedCore [.bool c, y.value, x.value] store
    check (decide (evaluateTypedLetReturnTreeWithCost? owner prepared.inputs.names prepared.inputs.environment source.value.body =
      some (x.value, cost))) "original selected raw value or independent cost changed"
    for fuel in List.range 21 do
      match atRun : runRuntimeFunction? old owner source args fuel store with
      | none => throw (IO.userError "successful preparation did not run")
      | some outcome =>
          have _ := runRuntimeFunction?_some_of_extends extension atRun
          check (decide (outcome = (x.type, Core.runStateful fuel start) ∧
            runRuntimeFunction? next owner source args fuel store = some outcome)) "full outcome or saved state changed"
          check (match outcome.2 with
            | .done value final => decide (cost ≤ fuel ∧ value = x.value ∧ final = store)
            | .outOfFuel _ => decide (fuel < cost)
            | _ => false) "independent exact cost threshold changed"
    for spent in List.range cost do
      match exhausted : runRuntimeFunction? old owner source args spent store with
      | some (_, .outOfFuel cp) =>
          have _ := runRuntimeFunction?_resume exhausted (cost - spent)
          check (decide (Core.runStateful (cost - spent) cp = .done x.value store)) "actual residual changed"
          if cost - spent > 1 then
            let .outOfFuel second := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) second = .done x.value store)) "three chunks lost captured data"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done x.value store) "restart substituted for resumption"
      | _ => throw (IO.userError "genuine checkpoint missing")
private def checkMutual (type : Core.Ty) (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO Unit := do
  have _ := bindRuntimeParameters?_eq_of_mutual_extends (forward type) (backward type) owner source.value.signature.parameters.elements args
  have _ := prepareRuntimeFunction?_eq_of_mutual_extends (forward type) (backward type) owner source args
  check (decide ((prepareRuntimeFunction? (table type) owner source args).map payload =
    (prepareRuntimeFunction? (alternate type) owner source args).map payload)) "mutual full preparation disagreed"
  for store in [[], [w 91]] do
    for fuel in List.range 21 do
      have _ := runRuntimeFunction?_eq_of_mutual_extends (forward type) (backward type) owner source args fuel store
      check (decide (runRuntimeFunction? (table type) owner source args fuel store =
        runRuntimeFunction? (alternate type) owner source args fuel store)) "mutual None or full run result changed"
private def checked (type : Core.Ty) (x y : Core.Value) (xt : Core.ValueHasType x type) (yt : Core.ValueHasType y type) : IO Unit := do
  for annotated in [false, true] do
    for c in [false, true] do
      let content := text (mixedText annotated)
      verify (table type) (alternate type) (forward type) content ⟨type,x,xt⟩ ⟨type,y,yt⟩ c mixed (if c then 17 else 13) (mixedPaths x y c)
      verify (table type) (enlarged type) (TypeNameTable.Extends.append_right _ _) content ⟨type,x,xt⟩ ⟨type,y,yt⟩ c mixed (if c then 17 else 13) (mixedPaths x y c)
      checkMutual type (← parsed content) [⟨type,x,xt⟩, ⟨type,y,yt⟩, ⟨.bool,.bool c,.bool⟩]
end RuntimeTypeExtensionEntries
open RuntimeTypeExtensionEntries

def frontendParsedRuntimeTypeExtensionEntryTests : IO Unit := do
  checked .word (w 9) (w 2) .word .word
  checked .unit .unit .unit .unit .unit
  checked (.product .word .bool) (.pair (w 9) (.bool true)) (.pair (w 2) (.bool false)) (.pair .word .bool) (.pair .word .bool)
  checked (.cell .word) (.cellRef .word 700) (.cellRef .word 701) .cellRef .cellRef
  checked (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  let args : List TypedRuntimeArgument := [⟨.word,w 9,.word⟩, ⟨.word,w 2,.word⟩, ⟨.bool,.bool true,.bool⟩]
  for content in ["function f(x:Alias,y:T,c:Bool) returns(T){{return x;}}",
      "function f(x:T,y:T,c:Bool) returns(Alias){{return x;}}"] do
    let source ← parsed content
    check ((prepareRuntimeFunction? (table .word) owner source args).isNone) "unknown whole annotation unexpectedly accepted"
    checkMutual .word source args
    verify (enlarged .word) (enlarged .word) (TypeNameTable.Extends.refl _) content ⟨.word,w 9,.word⟩ ⟨.word,w 2,.word⟩ true (.var 2) 1
      (fun _ _ => .cons (.var rfl) .refl)
  let repairedText := text "{if(c){return x;}else{let z:Alias=y;return z;}}"
  let repaired ← parsed repairedText
  let original ← parameters (table .word) .empty repaired.value.signature.parameters.elements args
  check ((prepareRuntimeFunction? (table .word) owner repaired args).isNone &&
    decide (evaluateTypedLetReturnTreeWithCost? owner original.inputs.names original.inputs.environment repaired.value.body = some (w 9, 4)))
    "unselected unknown annotation confused raw execution with whole acceptance"
  verify (enlarged .word) (enlarged .word) (TypeNameTable.Extends.refl _) repairedText ⟨.word,w 9,.word⟩ ⟨.word,w 2,.word⟩ true
    (.ifE (.var 0) (.var 2) (.letE (.var 1) (.var 0))) 4
    (fun _ _ => .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl))))
  for content in [text "{if(c){return x;}else{missing;return y;}}",
      "function f<G>(x:T,y:T,c:Bool) returns(T){{return x;}}",
      "function f(x:T,x:T,c:Bool) returns(T){{return x;}}", "function f(x:T,y:T,c:Bool) returns(Bool){{return x;}}"] do
    let source ← parsed content
    check ((prepareRuntimeFunction? (table .word) owner source args).isNone) "whole gate relaxed"
    checkMutual .word source args
  let source ← parsed (text "{{return x;}}")
  for badArgs in [[], args.drop 1, args.reverse, args ++ [⟨.unit,.unit,.unit⟩]] do
    check ((prepareRuntimeFunction? (table .word) owner source badArgs).isNone) "argument gate relaxed"
    checkMutual .word source badArgs
  let changed : List TypedRuntimeArgument := [⟨.word,w 14,.word⟩, ⟨.word,w 2,.word⟩, ⟨.bool,.bool true,.bool⟩]
  let first ← prepare (table .word) source args; let second ← prepare (table .word) source changed
  have _ := prepareRuntimeFunction?_static_projection_eq (types := table .word) (owner := owner) (declaration := source)
    (leftArguments := args) (rightArguments := changed) (by rfl)
  check (decide (first.prepared.core = second.prepared.core ∧ first.prepared.returnType = second.prepared.returnType ∧
      first.prepared.inputs.context = second.prepared.inputs.context ∧ first.prepared.inputs.names = second.prepared.inputs.names) &&
    decide (rows first.prepared.inputs ≠ rows second.prepared.inputs) &&
    decide (runRuntimeFunction? (table .word) owner source args 1 [] = some (.word,.done (w 9) []) ∧
      runRuntimeFunction? (table .word) owner source changed 1 [] = some (.word,.done (w 14) [])))
    "equal argument types erased different actual values"
  for type in [Core.Ty.namedData ⟨90⟩, .product (.namedData ⟨90⟩) (.cell (.namedData ⟨13⟩))] do
    let source ← parsed (text (mixedText true))
    let some inputs := declareRuntimeParameters? (table type) owner source.value.signature.parameters.elements
      | throw (IO.userError "nominal static parameters demanded runtime values")
    let certified ← body (table type) inputs source.value.body
    have _ := certified.evidence.complete
    check (decide (certified.core = mixed ∧ certified.type = type ∧ inputs.context.values = [.bool,type,type]))
      "nominal independent static meaning changed"
  have _ : ¬ TypeNameTable.Extends (table .word) ((["T"], .bool) :: table .word) := by
    intro extension
    have wrong : Core.Ty.word = .bool := (extension (.head : TypeNameTable.Lookup (table .word) ["T"] .word)).type_unique .head
    cases wrong
end Tests
