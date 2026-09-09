import Solcore.Syntax.Parser.Function
import Solcore.Test.FrontendComputationScopeBoundaryProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.WordMatchProperties
import Solcore.Core.FuelResumptionProperties

/-! Original parsed branches distinguish scope guards from selected raw paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedScopedShadowingBoundaries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ShadowBoundary", by decide⟩], by decide⟩⟩, 73⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def inputs := (LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" .word
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def word := Core.Value.word (Core.Word.ofNatModulo 17)
private def env (choice : Bool) : Resolved.Environment := [(id 1, word), (id 0, .bool choice)]
private def parsed (body : String) (parameters : String := "") : IO Syntax.FunctionDecl := do
  let text := "function guard(" ++ parameters ++ "){" ++ body ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main, "shadow-boundary.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lex")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original source bytes"
  return source
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
          | some type, some index => return ⟨.var index, type, by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _, _ => throw (IO.userError "original row")
      | _ => throw (IO.userError "unresolved original name")
  | _ => throw (IO.userError "fixture child")
private structure Body (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveComputationReturnTreeElaborates types owner i b core type
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Body i b) := do
  for statement in b.value do check (b.span.contains statement.span) "original statement span"
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ =>
      let c ← child i s; return ⟨c.core, c.type, by rw [shape]; exact .expression c.evidence⟩
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let c ← body i ⟨inner, statements⟩; return ⟨c.core, c.type, by rw [shape]; exact .block c.evidence⟩
  | ⟨span, ⟨_, .letDecl name none (some init)⟩ :: rest⟩ =>
      let c ← child i init; let tail ← body (i.bindFresh owner name.value c.type) ⟨span, rest⟩
      return ⟨.letE c.core tail.core, tail.type, by rw [shape]; exact .inferred c.evidence tail.evidence⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← child i condition; let a ← body i yes; let d ← body i no
      if valid : c.type = .bool ∧ d.type = a.type then
        if guard : computationBlockPreservesNames (i.names.map Prod.fst) yes = true then
          return ⟨.ifE c.core a.core d.core, a.type, by
            rw [shape]
            exact .conditional (valid.1 ▸ c.evidence) (computationBlockPreservesNames_iff.mp guard)
              a.evidence (valid.2 ▸ d.evidence)⟩
        else throw (IO.userError "exposed then shadow")
      else throw (IO.userError "conditional types")
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨s, []⟩⟩ ⟨_, ⟨[], some defaultBody⟩⟩⟩]⟩ =>
      let c ← child i s; let d ← body i defaultBody
      return ⟨.letE c.core (d.core.weakenAt 0), d.type, by
        rw [shape]
        exact .wordMatch (entries := []) (defaultEntry := some (defaultBody, d.core)) c.evidence rfl (by simp)
          (.inr (by simp)) (by simp) rfl (by intro entry member; cases List.mem_singleton.mp member; exact d.evidence) rfl⟩
  | _ => throw (IO.userError "fixture body")
termination_by sizeOf b
private structure AtomValue (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table e store s value store 1
private def atomValue (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (AtomValue table e s) := do
  match shape : s with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match found : e.lookup? localId with
          | some value => return ⟨value, fun _ => by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
          | _ => throw (IO.userError "missing actual row")
      | _ => throw (IO.userError "missing actual name")
  | _ => throw (IO.userError "raw atom")
private structure Raw (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table e store b value store cost
private def raw (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) : IO (Raw table e b) := do
  match shape : b with
  | ⟨_, [⟨_, .returnStmt (some s)⟩]⟩ =>
      let c ← atomValue table e s; return ⟨c.value, 1, fun store => by rw [shape]; exact .expression (c.evidence store)⟩
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let c ← raw table e ⟨inner, statements⟩; return ⟨c.value, c.cost, fun store => by rw [shape]; exact .block (c.evidence store)⟩
  | ⟨span, ⟨_, .letDecl name none (some init)⟩ :: rest⟩ =>
      let c ← atomValue table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let d ← raw ((name.value, fresh) :: table) ((fresh, c.value) :: e) ⟨span, rest⟩
      return ⟨d.value, 1 + d.cost + 2, fun store => by rw [shape]; exact .inferred (c.evidence store) (d.evidence store)⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let c ← atomValue table e condition
      match selected : c.value with
      | .bool true => let d ← raw table e yes; return ⟨d.value, 1 + d.cost + 2,
          fun store => by rw [shape]; exact .ifTrue (selected ▸ c.evidence store) (d.evidence store)⟩
      | .bool false => let d ← raw table e no; return ⟨d.value, 1 + d.cost + 2,
          fun store => by rw [shape]; exact .ifFalse (selected ▸ c.evidence store) (d.evidence store)⟩
      | _ => throw (IO.userError "raw condition")
  | ⟨_, [⟨_, .matchWith ⟨_, ⟨s, []⟩⟩ ⟨_, ⟨[], some defaultBody⟩⟩⟩]⟩ =>
      let c ← atomValue table e s; let d ← raw table e defaultBody
      return ⟨d.value, 1 + d.cost + 2, fun store => by rw [shape]; exact .wordMatch (c.evidence store) .fallback (d.evidence store)⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def shadow : Core.Expr := .letE (.var 0) (.var 0)
private def matched : Core.Expr := .letE (.var 0) (.letE (.var 1) (.var 0))
private theorem shadowPath (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 4 ⟨.eval shadow (value :: retained), k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
private theorem matchPath (value : Core.Value) (retained : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 7 ⟨.eval matched (value :: retained), k, store⟩ ⟨.ret value, k, store⟩ :=
  CostStepComposition.letE (.cons (.var rfl) .refl)
    (CostStepComposition.letE (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
private def positive (text : String) (core : Core.Expr) (yesCost noCost : Nat)
    (manual : ∀ choice store k, Core.Steps (if choice then yesCost else noCost)
      ⟨.eval core (env choice).values, k, store⟩ ⟨.ret word, k, store⟩) : IO Unit := do
  let source ← parsed text; let b := source.value.body; let static ← body inputs b
  if fixed : static.core = core ∧ static.type = .word then
    have provenance : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by
      simpa only [fixed.1, fixed.2] using static.evidence
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
    have _ := ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType provenance
    check (decide (elaborateRecursiveComputationReturnTree? types owner inputs b = some (core, .word))) "exact original Core"
    for choice in [false, true] do
      let r ← raw inputs.names (env choice) b; let cost := if choice then yesCost else noCost
      if actual : r.value = word ∧ r.cost = cost then
        for store in [[], [Core.Value.bool true, .unit]] do
          have _ : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env choice) store b word store cost := by
            simpa only [actual.1, actual.2] using r.evidence store
          for fuel in List.range (cost + 2) do
            have _ := (manual choice store []).runStateful_done_iff (fuel := fuel)
            let result := Core.runStateful fuel (.initial core (env choice).values store)
            check (decide (result = .done word store) == decide (cost ≤ fuel)) "literal Core exact threshold"
            match result with
            | .outOfFuel checkpoint =>
                check (decide (Core.runStateful (cost - fuel) checkpoint = .done word store)) "genuine checkpoint/residual"
            | .done value finalStore => check (decide (value = word ∧ finalStore = store)) "actual retained store"
            | .fault _ _ => throw (IO.userError "unexpected fault")
      else throw (IO.userError "independent raw value/cost")
  else throw (IO.userError "independent source/Core mismatch")
private def rejection (text : String) : IO Unit := do
  let source ← parsed text; let b := source.value.body; let r ← raw inputs.names (env false) b
  check (decide (r.value = word ∧ r.cost = 4 ∧ elaborateRecursiveComputationReturnTree? types owner inputs b = none)) "false selected path succeeds but static guard rejects"
  match shape : b with
  | ⟨bs, [⟨ss, .ifThen condition yes (some no)⟩]⟩ =>
      if failed : computationBlockPreservesNames (inputs.names.map Prod.fst) yes = false then
        have forbidden : ¬ ∃ core type, RecursiveComputationReturnTreeElaborates types owner inputs
            ⟨bs, [⟨ss, .ifThen condition yes (some no)⟩]⟩ core type := by
          obtain ⟨name, present, exposed⟩ := computationBlockPreservesNames_eq_false_iff.mp failed
          exact (FrontendComputationScopeBoundary.exposed_then_shadow_rejects_independently_of_child_checking
            elaborateRecursiveLocalComputation? RecursiveLocalComputationElaborates types owner inputs bs ss condition yes no name present exposed).2
        have _ := forbidden
        for store in [[], [Core.Value.bool true]] do have _ := r.evidence store; pure ()
      else throw (IO.userError "expected source occurrence witness")
  | _ => throw (IO.userError "original if shape")
end ParsedScopedShadowingBoundaries
open ParsedScopedShadowingBoundaries
def frontendParsedScopedShadowingBoundaryTests : IO Unit := do
  positive "if(c){{let x=x;return x;}}else{return x;}" (.ifE (.var 1) shadow (.var 0)) 7 4 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (shadowPath _ _ _ _))
  positive "if(c){return x;}else{let x=x;return x;}" (.ifE (.var 1) (.var 0) shadow) 4 7 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (shadowPath _ _ _ _)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (.cons (.var rfl) .refl))
  positive "if(c){match(x){default{let x=x;return x;}}}else{return x;}" (.ifE (.var 1) matched (.var 0)) 10 4 (by
    intro choice store k; cases choice
    · exact CostStepComposition.ifFalse (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    · exact CostStepComposition.ifTrue (.cons (.var rfl) .refl) (matchPath _ _ _ _))
  rejection "if(c){let x=x;return x;}else{return x;}"
  rejection "if(c){if(c){return x;}else{let x=x;return x;}}else{return x;}"
  for text in ["if(c){let y=x;return y;}else{return y;}", "let missing=missing;return missing;",
      "if(c){{let y=x;return y;}}else{return y;}", "{let x=x;}return x;"] do
    let source ← parsed text
    check ((elaborateRecursiveComputationReturnTree? types owner inputs source.value.body).isNone) "retained incomplete/outside profile"
  let source ← parsed "return x;" "x:Word,x:Word"
  check ((declareRuntimeParameters? types owner source.value.signature.parameters.elements).isNone) "original duplicate parameters remain rejected"
end Tests
