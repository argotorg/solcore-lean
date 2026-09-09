import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ComputationFunctionTypeExtensionProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Core.FuelResumptionProperties

/-! A selected raw success does not license rejection preservation when an
unselected original annotation gains or changes its first-match meaning. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationTypeTableBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TypeTableBoundary", by decide⟩], by decide⟩⟩, 127⟩
private def base : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def repaired : TypeNameTable := base ++ [(["Missing"], .word)]
private def changed : TypeNameTable := (["Missing"], .bool) :: repaired
private def word := Core.Value.word (Core.Word.ofNatModulo 17)
private def args (c : Bool) : List TypedRuntimeArgument := [⟨.bool, .bool c, .bool⟩, ⟨.word, word, .word⟩]
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.letE (.var 0) (.var 0))
private def cost (c : Bool) : Nat := if c then 4 else 7
private def payload (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)), p.core, p.returnType)
private theorem changed_not_extension : ¬ TypeNameTable.Extends repaired changed := by
  intro extension
  have found : TypeNameTable.Lookup repaired ["Missing"] .word := .tail (by decide) (.tail (by decide) .head)
  have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
  cases impossible
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function boundary(c:Bool,x:Word) returns(Word){if(c){return x;}else{let x:Missing=x;return x;}}"
  let file : Syntax.SourceFile := ⟨⟨.main, "computation-type-table-boundary.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lex")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original complete bytes"
  return source
private def meaning (s : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes repaired s t)) := do
  match shape : s with
  | ⟨_, .named name none⟩ =>
      match found : repaired.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t, ⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original named meaning")
  | _ => throw (IO.userError "original annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (as : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom repaired owner s ps statics
  bound : RuntimeParametersBindFrom repaired owner a ps as actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (as : List TypedRuntimeArgument) : IO (Parameters s a ps as) := do
  match shape : ps, supplied : as with
  | [], [] => return ⟨s, a, by rw [shape]; exact .nil, by rw [shape, supplied]; exact .nil⟩
  | ⟨span, .typed none name ann⟩ :: rest, arg :: tail =>
      check (span.contains name.span && span.contains ann.span) "original parameter fields"
      let m ← meaning ann
      if same : m.1 = arg.type then
        if fresh : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let n ← parameters (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨n.statics, n.actual, by rw [shape]; exact .cons (same ▸ m.2.down) fresh.1 n.declared,
            by rw [shape, supplied]; exact .cons (same ▸ m.2.down) fresh.2 n.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _, _ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context s)) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
          | some t, some n => return ⟨.var n, t, by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _, _ => throw (IO.userError "original row")
      | none => throw (IO.userError "original name")
  | _ => throw (IO.userError "child fixture")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates repaired owner i b)) := do
  check (b.value.all fun s => b.span.contains s.span) "original statement ranges"
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ => let c ← child i s; return ⟨c.core, c.type, by rw [shape]; exact .expression c.evidence⟩
  | ⟨span, ⟨ls, .letDecl name (some ann) (some init)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains ann.span && ls.contains init.span) "original annotation and initializer"
      let c ← child i init; let m ← meaning ann
      if same : m.1 = c.type then
        let n ← body (i.bindFresh owner name.value c.type) ⟨span, rest⟩
        return ⟨.letE c.core n.core, n.type, by rw [shape]; exact .binding (same ▸ m.2.down) c.evidence n.evidence⟩
      else throw (IO.userError "typed initializer")
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let a ← body i yes; let d ← body i no
      if same : c.type = .bool ∧ d.type = a.type then
        match arm : yes with
        | ⟨_, [⟨_, .returnStmt _⟩]⟩ =>
            have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by
              intro name exposed; rw [arm] at exposed; cases exposed with | tail impossible => cases impossible
            return ⟨.ifE c.core a.core d.core, a.type, by rw [shape]; exact .conditional (same.1 ▸ c.evidence) protection a.evidence (same.2 ▸ d.evidence)⟩
        | _ => throw (IO.userError "original return-only then")
      else throw (IO.userError "branch types")
  | _ => throw (IO.userError "body fixture")
termination_by sizeOf b
private def preparation (source : Syntax.FunctionDecl) (as : List TypedRuntimeArgument) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares repaired owner source as p ∧ p.core = core ∧ p.returnType = .word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements as
  let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1 = .word ∧ b.core = core ∧ b.type = .word then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have header : RuntimeFunctionHeader repaired source.value.signature .word :=
            ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compiled : RecursiveComputationFunctionCompiles repaired owner source ⟨ps.statics, core, .word⟩ :=
            ⟨header, ps.declared, by simpa only [erased, same.2.1, same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compiled
          check (decide (ps.actual.environment.values = as.reverse.map (·.value) ∧
            ps.actual.names = [("x", ⟨owner, 1⟩), ("c", ⟨owner, 0⟩)])) "exact declaration order and actual values"
          return ⟨⟨ps.actual, core, .word⟩, ⟨⟨⟨header, ps.bound, by simpa only [same.2.1, same.2.2] using b.evidence⟩, rfl, rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "separately written Core")
  | _ => throw (IO.userError "original return clause")
private def atom (table : LocalNameTable) (env : Resolved.Environment) (s : Syntax.Expr) :
    IO (Σ v, PLift (∀ store, RecursiveLocalComputationEvaluatesWithCost table env store s v store 1)) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | some id => match found : env.lookup? id with
        | some v => return ⟨v, ⟨fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩⟩
        | none => throw (IO.userError "raw row")
      | none => throw (IO.userError "raw name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (env : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table env store b value store cost
private def raw (table : LocalNameTable) (env : Resolved.Environment) (b : Syntax.Block) : IO (Raw table env b) := do
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ => let v ← atom table env s; return ⟨v.1, 1, fun _ => by rw [shape]; exact .expression (v.2.down _)⟩
  | ⟨span, ⟨_, .letDecl name (some _) (some init)⟩ :: rest⟩ =>
      let v ← atom table env init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← raw ((name.value, fresh) :: table) ((fresh, v.1) :: env) ⟨span, rest⟩
      return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .binding (v.2.down _) (r.evidence _)⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← atom table env condition
      match selected : c.1 with
      | .bool true => let r ← raw table env yes; return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .ifTrue (selected ▸ c.2.down _) (r.evidence _)⟩
      | .bool false => let r ← raw table env no; return ⟨r.value, 1 + r.cost + 2, fun _ => by rw [shape]; exact .ifFalse (selected ▸ c.2.down _) (r.evidence _)⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem path (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost c) ⟨.eval core [word, .bool c], k, store⟩ ⟨.ret word, k, store⟩ := by
  cases c
  · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl)
      (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
  · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
end ParsedComputationTypeTableBoundaries
open ParsedComputationTypeTableBoundaries
def frontendParsedComputationTypeTableBoundaryTests : IO Unit := do
  let source ← parsed
  have extension : TypeNameTable.Extends base repaired := TypeNameTable.Extends.append_right _ _
  have _ := changed_not_extension
  check (decide (base.lookup? ["Missing"] = none ∧ repaired.lookup? ["Missing"] = some .word ∧
    changed.lookup? ["Missing"] = some .bool)) "unknown repair and changed first match are different boundaries"
  for c in [true, false] do
    let p ← preparation source (args c); let prepared := p.1; let evidence := p.2.down.1
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr evidence
    have _ := evidence.extend_types (TypeNameTable.Extends.append_right repaired [(["Word"], .bool)])
    have _ : TypeNameTable.Lookup repaired ["Word"] .word := extension .head
    let r ← raw prepared.inputs.names prepared.inputs.environment source.value.body
    if expected : r.value = word ∧ r.cost = cost c then
      if rejected : elaborateRecursiveComputationReturnTree? base owner prepared.inputs.toTypeInputs source.value.body = none then
        have absent : ¬ ∃ e t, RecursiveComputationReturnTreeElaborates base owner prepared.inputs.toTypeInputs source.value.body e t := by
          rintro ⟨e, t, provenance⟩
          have contradiction := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
          change elaborateRecursiveComputationReturnTree? base owner prepared.inputs.toTypeInputs source.value.body = some (e, t) at contradiction
          rw [rejected] at contradiction; cases contradiction
        have _ := absent
      else throw (IO.userError "old whole body accepted its unknown unselected annotation")
      for table in [base, changed] do
        check ((compileRecursiveComputationFunction? table owner source).isNone &&
          (prepareRecursiveComputationFunction? table owner source (args c)).isNone) "whole source rejection cannot follow the selected path"
      for store in [[], [Core.Value.bool true, .cellRef .word 999]] do
        have sourceCost : RecursiveComputationReturnTreeEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment store source.value.body word store (cost c) := by
          simpa only [expected.1, expected.2] using r.evidence store
        have _ := sourceCost
        for fuel in List.range (cost c + 2) do
          have _ := (path c store []).runStateful_done_iff (fuel := fuel)
          let result := Core.runStateful fuel (.initial core [word, .bool c] store)
          check (decide (runRecursiveComputationFunction? repaired owner source (args c) fuel store = some (.word, result))) "complete repaired result equals independent literal path"
          check (decide (runRecursiveComputationFunction? base owner source (args c) fuel store = none ∧
            runRecursiveComputationFunction? changed owner source (args c) fuel store = none)) "rejected original annotations stay rejected at every fuel"
          check (decide (result = .done word store) == decide (cost c ≤ fuel)) "independent exact source cost"
          match result with
          | .outOfFuel cp => check (decide (Core.runStateful (cost c - fuel) cp = .done word store)) "genuine residual retains original values/store"
          | .done _ _ => pure ()
          | .fault _ _ => throw (IO.userError "unexpected fault")
    else throw (IO.userError "independent selected raw value and cost")
    check (decide ((prepareRecursiveComputationFunction? repaired owner source (args c)).map payload = some (payload prepared))) "original independent preparation"
    have _ := accepted
  for badArgs in [[], [⟨.bool, .bool true, .bool⟩], [⟨.bool, .bool true, .bool⟩, ⟨.bool, .bool false, .bool⟩]] do
    check ((prepareRecursiveComputationFunction? repaired owner source badArgs).isNone) "repair does not repair wrong actual arity or types"
end Tests
