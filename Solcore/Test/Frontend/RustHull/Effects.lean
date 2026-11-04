import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported
import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.ContractHashExecutionCorrespondence
import Solcore.Abi.Keccak256
import Solcore.Frontend.RustHull.LogsSemantics
import Solcore.Frontend.RustHull.ContractLogExecutionCorrespondence
import Solcore.Frontend.RustHull.MemoryCopySemantics
import Solcore.Frontend.RustHull.ContractCopyExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractMemoryExecutionCorrespondence
import Solcore.Frontend.RustHull.MemorySnapshot
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.ContractCallExecutionCorrespondence

/-!
# Hull effect correspondence tests

Decoding, memory copying, logs, Keccak, inline assembly and precompile calls, from independent
derivations through public execution.
-/

section
-- leanmerge: from Solcore.Test.RustHullAssemblyCorrespondence
/-! Inline Yul blocks of one builtin call on two literal words reach the actual
Yul lowering, memory writes and terminations through the call-mode public
theorem. Each scenario writes memory in one block and ends the frame in a
second: an `mstore` returned as a word, an `mstore8` of a hexadecimal byte, an
`mstore` whose last byte is reverted, and an `mstore` of the literal `true`
whose last byte is returned. The independent source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullAssemblyCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | stored | byte | reverted | flag
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def block (name : String) (first second : YulExpr) : Stmt :=
  ⟨.assembly [⟨.expression ⟨.call ⟨name, none⟩ [first, second], none⟩, none⟩], none⟩

def rootBytes : List UInt8 := [0]
def writing : Scenario → Stmt
  | .stored => block "mstore" (number "0") (number "42")
  | .byte => block "mstore8" (number "31") ⟨.literal (.hex "0xff"), none⟩
  | .reverted => block "mstore" (number "0") (number "7")
  | .flag => block "mstore" (number "0") ⟨.literal (.bool true), none⟩
def ending : Scenario → Stmt
  | .reverted => block "revert" (number "31") (number "1")
  | .flag => block "return" (number "31") (number "1")
  | _ => block "return" (number "0") (number "32")
def code (scenario : Scenario) : CodeBlock := {stmts := [writing scenario, ending scenario], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Assembler" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withFrame (state : SourceState) (next : RuntimeEffectsSemantics.State) : SourceState :=
  {state with external := {state.external with
    runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime next)}}
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effect of each scenario's two blocks. -/
def write : Scenario → RuntimeEffectsSemantics.State → RuntimeEffectsSemantics.State
  | .stored, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 42)).2}
  | .byte, current => {current with memory := (MemorySemantics.mstore8 current.memory (w 31) (w 255)).2}
  | .reverted, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 7)).2}
  | .flag, current => {current with memory := (MemorySemantics.mstore current.memory (w 0) (w 1)).2}
def exit : Scenario → RuntimeEffectsSemantics.State → RuntimeEffectsSemantics.State
  | .reverted, current => (TerminationSemantics.terminate current 2 (w 31) (w 1)).2
  | .flag, current => (TerminationSemantics.terminate current 1 (w 31) (w 1)).2
  | _, current => (TerminationSemantics.terminate current 1 (w 0) (w 32)).2
def written (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withFrame (initial object) (write scenario (frame (initial object)))
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withFrame (written object scenario) (exit scenario (frame (written object scenario)))
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem write_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (writing scenario) (initial object) .fallthrough
      (written object scenario) := by
  cases scenario
  · exact .assembly rfl (YulSemantics.Run.expression (YulSemantics.Eval.call
      (.cons (.literal (word := w 42) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .mstore) .nil)
  · exact .assembly rfl (YulSemantics.Run.expression (YulSemantics.Eval.call
      (.cons (.literal (word := w 255) (by decide +kernel)) (.cons (.literal (word := w 31) (by decide +kernel)) .nil))
      .mstore8) .nil)
  · exact .assembly rfl (YulSemantics.Run.expression (YulSemantics.Eval.call
      (.cons (.literal (word := w 7) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .mstore) .nil)
  · exact .assembly rfl (YulSemantics.Run.expression (YulSemantics.Eval.call
      (.cons (.literal (word := w 1) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .mstore) .nil)

private theorem exit_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalStmt (functions scenario) effects [] (ending scenario) (written object scenario)
      (.fault (.language Core.Word.maximum)) (finalState object scenario) := by
  cases scenario
  · exact .assembly rfl (YulSemantics.Run.expressionFault (YulSemantics.Eval.call
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .returned))
  · exact .assembly rfl (YulSemantics.Run.expressionFault (YulSemantics.Eval.call
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
      .returned))
  · exact .assembly rfl (YulSemantics.Run.expressionFault (YulSemantics.Eval.call
      (.cons (.literal (word := w 1) (by decide +kernel)) (.cons (.literal (word := w 31) (by decide +kernel)) .nil))
      .reverted))
  · exact .assembly rfl (YulSemantics.Run.expressionFault (YulSemantics.Eval.call
      (.cons (.literal (word := w 1) (by decide +kernel)) (.cons (.literal (word := w 31) (by decide +kernel)) .nil))
      .returned))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  all_goals
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (write_source object _)
    exact .stop (by intros; intro impossible; cases impossible) (exit_source object _)
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "mstore8", "return", "revert"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals
    cases scenario
    all_goals
      simp only [writing, ending, block, number, ExecutableStatement]
      refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
      intro statement member
      simp only [List.mem_singleton] at member
      subst member
      exact .expression (.call (.inl (available _ (by simp [usedNames]))) (.cons .literal (.cons .literal .nil)))

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.reverted, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul: memory writes by
`mstore` and `mstore8` on number, hexadecimal and Boolean literals, followed by
`return` or `revert` blocks. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
    (source object scenario)

private def expected : Scenario → List UInt8
  | .stored => List.replicate 31 0 ++ [42]
  | .byte => List.replicate 31 0 ++ [255]
  | .reverted => [7]
  | .flag => [1]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"assembly correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"assembly correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match scenario, receipt.outcome with
    | .reverted, .reverted bytes =>
        unless bytes == expected scenario do
          throw (IO.userError s!"assembly correspondence: wrong revert bytes: {reprStr bytes}")
    | .reverted, outcome =>
        throw (IO.userError s!"assembly correspondence: unexpected outcome for reverted: {reprStr outcome}")
    | _, .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"assembly correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | _, outcome =>
        throw (IO.userError s!"assembly correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.stored, .byte, .reverted, .flag] do
    check scenario

end Tests.RustHullAssemblyCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullDecode
/-! Import-boundary regressions for complete Hull transport and strict rejection. -/
set_option autoImplicit false
namespace Tests.RustHullDecode
open Lean Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sample : String := r#"{
  "schema":"solcore-rs.hull.v1",
  "upstreamCommit":"e2eef19409fc8879cd4a9cc342ed60e3152f72c0",
  "program":{
    "entryPoints":["entry"],
    "span":{"file":"main.sol","start":0,"end":120},
    "functions":[{
      "name":"entry",
      "args":[{"name":"x","ty":{"tag":"named","name":"N","inner":{"tag":"sum","left":{"tag":"unit"},"right":{"tag":"word"}}}}],
      "ret":{"tag":"word","span":{"file":"main.sol","start":30,"end":34}},
      "body":[{
        "tag":"match","target":{"tag":"word"},
        "scrutinee":{"tag":"var","ty":{"tag":"namedRef","name":"N"},"name":"x"},
        "alts":[{
          "pat":{"tag":"con","value":{"tag":"inK","index":1}},"binder":"payload",
          "body":[{"tag":"return","value":{"tag":"word","ty":{"tag":"word"},"value":"0xffff"}}]
        }]
      }]
    }],
    "objects":[{
      "name":"Deployment","code":{"functions":[],"stmts":[{
        "tag":"assembly","body":[{
          "tag":"function","name":{"name":"choose"},"params":[{"name":"a"}],"rets":[{"name":"b"}],
          "body":[{
            "tag":"switch","value":{"tag":"ident","name":{"name":"a"}},
            "cases":[{"lit":{"tag":"number","value":"0"},"body":[{"tag":"assign","names":[{"name":"b"}],"value":{"tag":"literal","value":{"tag":"hex","value":"0xff"}}}]}],
            "defaultBody":null
          },{"tag":"leave"}]
        },{
          "tag":"let","names":[{"name":"result"}],
          "init":{"tag":"call","name":{"name":"choose","span":{"file":"main.sol","start":98,"end":104}},"args":[{"tag":"literal","value":{"tag":"number","value":"0"}}]}
        }]
      }]},
      "inners":[{"name":"Runtime","code":{"stmts":[],"functions":[]},"inners":[]}]
    }]
  }
}"#

private def put (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | _ => json

private def rejects (json : Json) (path : String) (limits : DecodeLimits := {}) : IO Unit :=
  match decode json limits with
  | .ok _ => throw (IO.userError s!"Hull decoder accepted malformed input at {path}")
  | .error error => require (error.path == path)
      s!"Hull decoder error path changed: expected {path}, got {reprStr error}"

/-- Generated pattern matches contain statement objects inside body arrays;
even a moderate Hull nesting depth therefore exceeds 256 JSON levels. -/
private def nestedStatements (count : Nat) (leaf : String := "{\"tag\":\"comment\",\"text\":\"leaf\"}") : String :=
  (List.range count).foldl (fun body _ => "{\"tag\":\"block\",\"body\":[" ++ body ++ "]}") leaf

private def nestedProgram (count : Nat) (leaf : String := "{\"tag\":\"comment\",\"text\":\"leaf\"}") : String :=
  "{\"schema\":\"" ++ schemaName ++ "\",\"upstreamCommit\":\"" ++ upstreamCommit ++
  "\",\"program\":{\"entryPoints\":[],\"objects\":[],\"functions\":[{\"name\":\"deep\",\"args\":[]," ++
  "\"ret\":{\"tag\":\"unit\"},\"body\":[" ++ nestedStatements count leaf ++ "]}]}}"

private def blockDepth : List Stmt → Nat
  | [{kind := .block body, ..}] => blockDepth body + 1
  | _ => 0

private def deepInputs : IO Unit := do
  let deep := nestedProgram 140
  let decoded ← match decodeText deep with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"Hull decoder rejected generated-depth input: {reprStr error}")
  match decoded.program.functions with
  | [function] =>
    require (blockDepth function.body == 140) "Hull decoder truncated generated nested statements"
  | _ => throw (IO.userError "Hull decoder lost the nested function")
  match decodeText deep {maxDepth := 256} with
  | .error error =>
    require (error.message == "JSON nesting or numeric token limit exceeded")
      "Hull decoder stopped enforcing the caller's depth limit"
  | .ok _ => throw (IO.userError "Hull decoder ignored an explicit depth limit")
  -- Root, program, functions, function, body, comment, text have depth seven;
  -- each enclosing block adds an object and array. The leaf reaches 511 here.
  match decodeText (nestedProgram 252) {maxDepth := 511},
      decodeText (nestedProgram 252) {maxDepth := 510} with
  | .ok _, .error error =>
    require (error.message == "JSON depth budget exceeded")
      "Hull decoder did not count the deepest scalar leaf"
  | _, _ => throw (IO.userError "Hull decoder changed its exact depth boundary")
  match decodeText (nestedProgram 254) with
  | .error error =>
    require (error.message == "JSON nesting or numeric token limit exceeded")
      "Hull decoder parsed text beyond its default nesting limit"
  | .ok _ => throw (IO.userError "Hull decoder accepted excessive default nesting")
  match decodeText (nestedProgram 140 "{\"tag\":\"future\"}") with
  | .error error =>
    require (error.message == "unknown statement tag: future")
      "Hull decoder skipped validation of deeply nested statements"
  | .ok _ => throw (IO.userError "Hull decoder accepted an unknown nested statement")

def run : IO Unit := do
  let envelope ← match decodeText sample with
    | .ok value => pure value
    | .error error => throw (IO.userError (reprStr error))
  require (envelope.program.entryPoints == ["entry"]) "Hull decoder lost entry point order"
  require (envelope.program.span == some {file := "main.sol", start := 0, stop := 120})
    "Hull decoder lost resolved source provenance"
  let function ← match envelope.program.functions with
    | [function] => pure function
    | _ => throw (IO.userError "Hull decoder lost function boundaries")
  require (function.ret == .located {file := "main.sol", start := 30, stop := 34} .word)
    "Hull decoder dropped type provenance"
  require (function.args.map (·.ty) == [.named "N" (.sum .unit .word)])
    "Hull decoder changed argument annotations"
  let alt ← match function.body with
    | [{kind := .matchStmt .word scrutinee [alt], ..}] =>
      require (scrutinee.ty == .namedRef "N" && scrutinee.kind == .var "x")
        "Hull decoder changed recursive type references"
      pure alt
    | _ => throw (IO.userError "Hull decoder changed match structure")
  require (alt.pat.kind == .con (.inK 1) && alt.binder == "payload")
    "Hull decoder changed constructor indices or binders"
  match alt.body with
  | [{kind := .returnStmt value, ..}] =>
    require (value.ty == .word && value.kind == .word "0xffff")
      "Hull decoder changed literal text"
  | _ => throw (IO.userError "Hull decoder lost a return")
  let code ← match envelope.program.objects with
    | [.object "Deployment" code [.object "Runtime" inner [] none] none] =>
      require (inner.stmts.isEmpty && inner.functions.isEmpty) "Hull decoder changed inner code"
      pure code
    | _ => throw (IO.userError "Hull decoder changed nested objects")
  let assembly ← match code.stmts with
    | [{kind := .assembly assembly, ..}] => pure assembly
    | _ => throw (IO.userError "Hull decoder lost assembly")
  match assembly with
  | [{kind := .functionDef name params rets body, ..}, {kind := .letDecl names (some init), ..}] =>
    require (name.name == "choose" && params.map (·.name) == ["a"] && rets.map (·.name) == ["b"])
      "Hull decoder changed Yul function signatures"
    match body with
    | [{kind := .switch _ [arm] none, ..}, {kind := .leave, ..}] =>
      require (arm.lit == .number "0" && arm.body.length == 1) "Hull decoder changed switch cases"
    | _ => throw (IO.userError "Hull decoder changed Yul function scopes")
    require (names.map (·.name) == ["result"]) "Hull decoder changed Yul bindings"
    match init.kind with
    | .call name [_] =>
      require (name.name == "choose" && name.span == some {file := "main.sol", start := 98, stop := 104})
        "Hull decoder lost Yul identifier provenance"
    | _ => throw (IO.userError "Hull decoder changed Yul calls")
  | _ => throw (IO.userError "Hull decoder changed assembly boundaries")
  let json ← match Json.parse sample with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  rejects (put json "schema" (.str "other")) "$.schema"
  rejects (put json "upstreamCommit" (.str "unreviewed")) "$.upstreamCommit"
  rejects (put json "ignored" (.bool true)) "$.ignored"
  let program := json.getObjValD "program"
  rejects (put json "program" (put program "objects" (.str "lost"))) "$.program.objects"
  rejects (put json "program" (put program "span" (.mkObj [
    ("file", .str "main.sol"), ("start", toJson (9 : Nat)), ("end", toJson (1 : Nat))]))) "$.program.span"
  let unknown := Json.mkObj [("tag", .str "future"), ("ty", .mkObj [("tag", .str "unit")])]
  let function := Json.mkObj [("name", .str "main"), ("args", .arr #[]),
    ("ret", .mkObj [("tag", .str "unit")]),
    ("body", .arr #[.mkObj [("tag", .str "return"), ("value", unknown)]])]
  rejects (put json "program" (put program "functions" (.arr #[function])))
    "$.program.functions[0].body[0].value.tag"
  rejects json "$" {maxDepth := 0}
  rejects json "$" {maxNodes := 0}
  match decode json {maxStringBytes := 1} with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Hull decoder ignored string byte budget")
  match decodeText sample {maxInputBytes := 1}, decodeText "{", decodeText "[1e999999999]",
      decodeText "[[[[[]]]]]" {maxDepth := 3} with
  | .error _, .error _, .error _, .error _ => pure ()
  | _, _, _, _ => throw (IO.userError "Hull text decoder ignored byte, syntax, numeric, or nesting limits")
  deepInputs

end Tests.RustHullDecode
end

section
-- leanmerge: from Solcore.Test.RustHullKeccakCorrespondence
/-! Independent Keccak derivations reach public execution and repeated resume.
The output is stored beyond the hashed range, so the receipt and the original
memory bytes can both be checked against the source computation. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullKeccakCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | empty | unaligned | rate | multiple | overflow
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def offsetText : Scenario → String | .empty | .overflow => maximum | _ => "7"
def lengthText : Scenario → String
  | .empty => "0" | .unaligned => "3" | .rate => "136" | .multiple => "137" | .overflow => "1"
def offset : Scenario → Core.Word | .empty | .overflow => Core.Word.maximum | _ => w 7
def count : Scenario → Nat
  | .empty => 0 | .unaligned => 3 | .rate => 136 | .multiple => 137 | .overflow => 1
def hashCall (scenario : Scenario) : Expr := call .word "keccak256" [word (offsetText scenario), word (lengthText scenario)]
def seed : Expr := call .unit "mstore8" [word "7", word "171"]
def saveHash (scenario : Scenario) : Expr := call .unit "mstore" [word "192", hashCall scenario]
def returnHash : Expr := call .unit "return" [word "192", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (saveHash scenario), expression returnHash]
  functions := []
}
def program (scenario : Scenario) : Program := {
  entryPoints := [], functions := [], objects := [.object "Hash" (code scenario) []]
}
def context : Contract.Context := {}
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 7) (w 171)).2
def firstBlock (scenario : Scenario) : KeccakSemantics.State :=
  KeccakSemantics.permute (KeccakSemantics.absorbBlock seeded.words (offset scenario) (w (count scenario)) (List.replicate 25 Core.Word.zero))
def digest (scenario : Scenario) : Core.Word :=
  if count scenario < 136 then KeccakSemantics.digest (firstBlock scenario)
  else KeccakSemantics.digest (KeccakSemantics.permute (KeccakSemantics.absorbBlock seeded.words
    ((offset scenario).add (w 136)) ((w (count scenario)).sub (w 136)) (firstBlock scenario)))
def touchedSize : Scenario → Core.Word
  | .empty | .unaligned | .overflow => w 32
  | .rate | .multiple => w 160

def hashed (scenario : Scenario) : MemorySemantics.State := {seeded with size := touchedSize scenario}
def saved (scenario : Scenario) : MemorySemantics.State := (MemorySemantics.mstore (hashed scenario) (w 192) (digest scenario)).2

def initial (object : Contract.CompiledObject) : Semantics.State RuntimeHashEffectsSemantics.State :=
  ⟨[], ContractHashCorrespondence.contextInitialState object (Contract.normalizeContext context)⟩
def memoryState (object : Contract.CompiledObject) (memory : MemorySemantics.State) : Semantics.State RuntimeHashEffectsSemantics.State :=
  ⟨[], RuntimeHashEffectsSemantics.withMemory (initial object).external memory⟩
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeHashEffectsSemantics.State :=
  if scenario = .overflow then memoryState object seeded
  else ⟨[], RuntimeFullEffectsSemantics.withRuntime (memoryState object (saved scenario)).external
    (TerminationSemantics.terminate (memoryState object (saved scenario)).external.runtime.runtime 1 (w 192) (w 32)).2⟩
def reason (scenario : Scenario) : Core.Word := if scenario = .overflow then w 6 else Core.Word.maximum
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

theorem absorbed (scenario : Scenario) :
    KeccakSemantics.Absorb seeded.words (offset scenario) (w (count scenario))
      (List.replicate 25 Core.Word.zero) (digest scenario) := by
  cases scenario
  case empty => exact .last _ _ _ (by decide +kernel)
  case unaligned => exact .last _ _ _ (by decide +kernel)
  case rate => exact .more (by decide +kernel) (.last _ _ _ (by decide +kernel))
  case multiple => exact .more (by decide +kernel) (.last _ _ _ (by decide +kernel))
  case overflow => exact .last _ _ _ (by decide +kernel)

theorem hashing (scenario : Scenario) :
    KeccakSemantics.Hash (offset scenario) (w (count scenario)) seeded
      (if scenario = .overflow then MemorySemantics.overflow else .value (.word (digest scenario)))
      (if scenario = .overflow then seeded else hashed scenario) := by
  cases scenario
  case overflow => exact .overflow (by decide +kernel)
  all_goals exact .done (by decide +kernel) (absorbed _)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] seed
      (initial object) (.value .unit) (memoryState object seeded) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime rfl))))

private theorem hash_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] (hashCall scenario)
      (memoryState object seeded)
      (if scenario = .overflow then MemorySemantics.overflow else .value (.word (digest scenario)))
      (memoryState object (if scenario = .overflow then seeded else hashed scenario)) := by
  cases scenario
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .empty)))
  case unaligned =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "3") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .unaligned)))
  case rate =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "136") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .rate)))
  case multiple =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "137") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .multiple)))
  case overflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.hash (.hash (hashing .overflow)))


private theorem save_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : scenario ≠ .overflow) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] (saveHash scenario)
      (memoryState object seeded) (.value .unit) (memoryState object (saved scenario)) := by
  have hashedSource := hash_source object scenario
  simp only [successful, ↓reduceIte] at hashedSource
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "192") rfl) (.cons hashedSource .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeHashEffectsSemantics.Builtin.runtime
    apply RuntimeCopyEffectsSemantics.Builtin.runtime
    apply RuntimeFullEffectsSemantics.Builtin.runtime
    apply RuntimeLogEffectsSemantics.Builtin.runtime
    cases scenario <;> first | contradiction | rfl

private theorem overflow_source (object : Contract.CompiledObject) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code .overflow)] RuntimeHashEffectsSemantics.effects [] (saveHash .overflow)
      (memoryState object seeded) MemorySemantics.overflow (memoryState object seeded) := by
  apply Semantics.EvalExpr.callFault rfl
  exact .cons (.word (text := "192") rfl) (.fault (hash_source object .overflow))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : scenario ≠ .overflow) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects [] returnHash
      (memoryState object (saved scenario)) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, ↓reduceIte]
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "192") rfl) (.cons (.word (text := "32") rfl) .nil)
  · apply Semantics.EvalCall.external (by rfl) rfl
    exact .runtime (.runtime (.termination rfl))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeHashEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario))
  by_cases successful : scenario = .overflow
  · subst scenario
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (overflow_source object))
      (by intro impossible; cases impossible)
  · apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (save_source object scenario successful))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
      (by intro impossible; cases impossible)

private theorem hash_eligible (scenario : Scenario) :
    ExecutableExpression ContractHashCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (hashCall scenario) := by
  apply ExecutableExpression.external (name := "keccak256") (Or.inr rfl) (by rfl)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .word _ _ _

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractHashCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩)))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "mstore")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store, rfl⟩)))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · exact hash_eligible scenario
  · apply ExecutableExpression.external (name := "return")
      (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Hash"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Hash"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractHashCorrespondence.PublicMessageRel context (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractHashCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def bytes (scenario : Scenario) : List UInt8 :=
  if count scenario = 0 then [] else 171 :: List.replicate (count scenario - 1) 0
private def referenceDigest (scenario : Scenario) : ByteArray := Abi.V1.Keccak256.hash (bytes scenario).toByteArray
private def referenceWord (scenario : Scenario) : Core.Word :=
  w ((referenceDigest scenario).data.foldl (fun value byte => value * 256 + byte.toNat) 0)

private def checkTouchedMemory (scenario : Scenario) : IO Unit := do
  let expression := Core.Expr.letE
    (.newCell Core.WordMapping.type (Core.WordMapping.literal seeded.words))
    (.letE (.newCell .word (.word seeded.size))
      (Core.LanguageResult.bind (.product .word .word)
        (Keccak.hash (.var 1) (.var 0) (.word (offset scenario)) (.word (w (count scenario))))
        (Core.LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))))
  let expected := if scenario = .overflow then Core.Value.inLeft (.product .word .word) (.word (w 6))
    else .inRight .word (.pair (.word (digest scenario)) (.word (touchedSize scenario)))
  match Core.runStateful 10000000 (Core.State.initial expression) with
  | .done value store =>
      unless value == expected && store[0]? == some (Core.WordMapping.encode seeded.words) &&
          store[1]? == some (.word (touchedSize scenario)) do
        throw (IO.userError "hash correspondence: hash changed memory or touched the wrong extent")
  | outcome => throw (IO.userError s!"hash correspondence: direct hash failed: {reprStr outcome}")

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Hash"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"hash correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"hash correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 23).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"hash correspondence: short resume completed: {reprStr outcome}")
  let receipt := Contract.resumeWithReceipt checkpoint 10000000
  if scenario = .overflow then
    match receipt.outcome with
    | .languageFailure (.word reason) =>
        unless reason == w 6 && receipt.world.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "hash correspondence: overflow reason or receipt differs")
    | outcome => throw (IO.userError s!"hash correspondence: expected overflow, got {reprStr outcome}")
  else
    unless digest scenario == referenceWord scenario do
      throw (IO.userError "hash correspondence: independent source digest differs from the ABI hash")
    match receipt.outcome with
    | .returned returned storage =>
        unless returned == (referenceDigest scenario).data.toList && storage.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "hash correspondence: returned digest or empty effects differ")
    | outcome => throw (IO.userError s!"hash correspondence: expected returned digest, got {reprStr outcome}")
  match Core.runStateful 10000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair size (.pair memory _))))) _ =>
      let expected := (finalState object scenario).external.runtime.runtime
      unless memory == Core.WordMapping.encode expected.memory.words && exit == .word expected.storage.exit &&
          offset == .word expected.storage.returnOffset && size == .word expected.storage.returnSize do
        throw (IO.userError "hash correspondence: public snapshot differs from independent execution")
      for index in List.range 6 do
        unless MemorySemantics.lookup (w index) expected.memory.words == MemorySemantics.lookup (w index) seeded.words do
          throw (IO.userError "hash correspondence: hashing or padding changed input memory")
  | outcome => throw (IO.userError s!"hash correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  unless referenceWord .empty == w 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 do
    throw (IO.userError "hash correspondence: empty Keccak reference vector changed")
  for scenario in [Scenario.empty, .unaligned, .rate, .multiple, .overflow] do
    checkTouchedMemory scenario
    check scenario

end Tests.RustHullKeccakCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullLogDerivations
/-! Concrete independent event derivations: an unaligned 33-byte snapshot,
followed by a changed memory byte and a second one-byte event. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
namespace Tests.RustHullLogDerivations
open Solcore Solcore.Frontend.RustHull

abbrev word := Core.Word.ofNatModulo

def firstMemory : MemorySemantics.State :=
  (MemorySemantics.mstore8 {} (word 1) (word 171)).2

def firstWords (address : Core.Word) : LogsSemantics.Words :=
  [(word 0, address), (word 1, word 1), (word 2, word 33), (word 3, word 7),
    (word 4, LogsSemantics.paddedWord firstMemory.words (word 1) (word 33)),
    (word 5, LogsSemantics.paddedWord firstMemory.words (word 33) (word 1))]

def beforeFirst (address : Core.Word) : LogsSemantics.State :=
  {memory := firstMemory, address := address}

def afterFirst (address : Core.Word) : LogsSemantics.State :=
  {beforeFirst address with memory := {firstMemory with size := word 64}, words := firstWords address, cursor := word 6}

theorem first_append (address : Core.Word) :
    LogsSemantics.Append (word 1) (word 33) [word 7] (beforeFirst address) (.value .unit) (afterFirst address) := by
  apply LogsSemantics.Append.done (size := word 64) (words := firstWords address)
  · decide
  · change ¬word 0 > LogsSemantics.nextCursor (word 0) (word 33) [word 7]
    decide
  · change MemorySemantics.touchSize? firstMemory.size (word 1) (word 33) = some (word 64)
    decide
  · apply LogsSemantics.Copy.step (by decide)
    apply LogsSemantics.Copy.step (by decide)
    exact LogsSemantics.Copy.empty _ _ _

theorem first_execute (address : Core.Word) :
    LogsSemantics.Execute (word 1) (word 33) [word 7] (beforeFirst address) (.value .unit) (afterFirst address) :=
  .writable rfl (first_append address)

def overwrittenMemory : MemorySemantics.State :=
  (MemorySemantics.mstore8 {firstMemory with size := word 64} (word 1) (word 205)).2

def beforeSecond (address : Core.Word) : LogsSemantics.State :=
  {afterFirst address with memory := overwrittenMemory}

def secondWords (address : Core.Word) : LogsSemantics.Words :=
  firstWords address ++ [(word 6, address), (word 7, word 0), (word 8, word 1), (word 9, LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1))]

def afterSecond (address : Core.Word) : LogsSemantics.State :=
  {beforeSecond address with words := secondWords address, cursor := word 10}

theorem second_append (address : Core.Word) :
    LogsSemantics.Append (word 1) (word 1) [] (beforeSecond address) (.value .unit) (afterSecond address) := by
  apply LogsSemantics.Append.done (size := word 64) (words := secondWords address)
  · decide
  · change ¬word 6 > LogsSemantics.nextCursor (word 6) (word 1) []
    decide
  · change MemorySemantics.touchSize? overwrittenMemory.size (word 1) (word 1) = some (word 64)
    decide
  · apply LogsSemantics.Copy.step (by decide)
    exact LogsSemantics.Copy.empty _ _ _

theorem second_execute (address : Core.Word) :
    LogsSemantics.Execute (word 1) (word 1) [] (beforeSecond address) (.value .unit) (afterSecond address) :=
  .writable rfl (second_append address)

theorem first_payload_retained (address : Core.Word) :
    MemorySemantics.lookup (word 4) (secondWords address) = LogsSemantics.paddedWord firstMemory.words (word 1) (word 33) := by
  rfl

theorem second_payload_changed (address : Core.Word) :
    MemorySemantics.lookup (word 9) (secondWords address) = LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1) := by
  rfl


theorem first_payload_value :
    LogsSemantics.paddedWord firstMemory.words (word 1) (word 33) = word (171 * 256 ^ 31) := by
  decide +kernel

theorem first_tail_zero :
    LogsSemantics.paddedWord firstMemory.words (word 33) (word 1) = word 0 := by
  decide +kernel

theorem second_payload_value :
    LogsSemantics.paddedWord overwrittenMemory.words (word 1) (word 1) = word (205 * 256 ^ 31) := by
  decide +kernel

end Tests.RustHullLogDerivations
end

section
-- leanmerge: from Solcore.Test.RustHullLogCorrespondence
/-! An unaligned event captures its bytes before later memory writes. The same
independent source derivation reaches public completion, failure and resumption. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullLogCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def memoryWrite : Expr := call "mstore8" .unit [word "1", word "171"]
def firstLog : Expr := call "log1" .unit [word "1", word "33", word "7"]
def memoryOverwrite : Expr := call "mstore8" .unit [word "1", word "205"]
def secondLog : Expr := call "log0" .unit [word "1", word "1"]
def gas : Expr := call "gas" .word []
def code : CodeBlock := {
  stmts := [expression memoryWrite, expression firstLog, expression memoryOverwrite, expression secondLog, expression gas]
  functions := []
}
def program : Program := {entryPoints := [], functions := [], objects := [.object "Logs" code []]}
def context (missingGas isStatic : Bool) : Contract.Context := {
  address := Core.Word.ofNatModulo (2 ^ 160 + 11)
  isStatic := isStatic
  availableGas := if missingGas then none else some (Core.Word.ofNatModulo 10000)
}
def initial (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], ContractLogCorrespondence.contextInitialState object (Contract.normalizeContext (context missingGas isStatic))⟩
def memoryWritten (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], {(initial object missingGas isStatic).external with runtime :=
    {(initial object missingGas isStatic).external.runtime with runtime :=
      {(initial object missingGas isStatic).external.runtime.runtime with memory := RustHullLogDerivations.firstMemory}}}⟩
def firstLogged (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryWritten object missingGas false).external
    (RustHullLogDerivations.afterFirst (Core.Word.ofNatModulo 11))⟩
def memoryOverwritten (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], {(firstLogged object missingGas).external with runtime :=
    {(firstLogged object missingGas).external.runtime with runtime :=
      {(firstLogged object missingGas).external.runtime.runtime with memory := RustHullLogDerivations.overwrittenMemory}}}⟩
def secondLogged (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryOverwritten object missingGas).external
    (RustHullLogDerivations.afterSecond (Core.Word.ofNatModulo 11))⟩
def rejected (object : Contract.CompiledObject) (missingGas : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  ⟨[], RuntimeLogEffectsSemantics.withLogs (memoryWritten object missingGas true).external
    {RuntimeLogEffectsSemantics.logsState (memoryWritten object missingGas true).external with
      exit := Core.Word.ofNatModulo 3, returnOffset := Core.Word.zero, returnSize := Core.Word.zero}⟩
def finalState (object : Contract.CompiledObject) (missingGas isStatic : Bool) : Semantics.State RuntimeLogEffectsSemantics.State :=
  if isStatic then rejected object missingGas else secondLogged object missingGas

def result (missingGas isStatic : Bool) : Semantics.Result Semantics.Value :=
  if isStatic then .fault (.language Core.Word.maximum)
  else if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value .unit

private theorem memory_source (object : Contract.CompiledObject) (missingGas isStatic : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] memoryWrite
      (initial object missingGas isStatic) (.value .unit) (memoryWritten object missingGas isStatic) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime rfl)

private theorem first_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] firstLog
      (memoryWritten object missingGas false) (.value .unit) (firstLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) (.cons (.word (text := "7") rfl) .nil))
  · have observed : RuntimeLogEffectsSemantics.logsState (memoryWritten object missingGas false).external =
        RustHullLogDerivations.beforeFirst (Core.Word.ofNatModulo 11) := by
      change ({memory := RustHullLogDerivations.firstMemory, address := Contract.normalizeAddress (Core.Word.ofNatModulo (2 ^ 160 + 11))} : LogsSemantics.State) = _
      have normalized : Contract.normalizeAddress (Core.Word.ofNatModulo (2 ^ 160 + 11)) = Core.Word.ofNatModulo 11 := by decide +kernel
      rw [normalized]
      rfl
    apply Semantics.EvalCall.external (by rfl) rfl
    apply RuntimeLogEffectsSemantics.Builtin.logs
    apply LogsSemantics.Builtin.log .log1 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 33) [Core.Word.ofNatModulo 7] rfl
    rw [observed]
    exact RustHullLogDerivations.first_execute (Core.Word.ofNatModulo 11)

private theorem overwrite_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] memoryOverwrite
      (firstLogged object missingGas) (.value .unit) (memoryOverwritten object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "205") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime rfl)

private theorem second_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] secondLog
      (memoryOverwritten object missingGas) (.value .unit) (secondLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) .nil)
  · exact .external (by rfl) rfl (.logs (.log .log0 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 1) [] rfl (RustHullLogDerivations.second_execute (Core.Word.ofNatModulo 11))))

private theorem static_log_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] firstLog
      (memoryWritten object missingGas true) (.fault (.language Core.Word.maximum)) (rejected object missingGas) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) (.cons (.word (text := "7") rfl) .nil))
  · exact .external (by rfl) rfl (.logs (.log .log1 .unit (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 33) [Core.Word.ofNatModulo 7] rfl (.static rfl)))

private theorem gas_source (object : Contract.CompiledObject) (missingGas : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects [] gas
      (secondLogged object missingGas)
      (if missingGas then .fault (.language (Core.Word.ofNatModulo 9)) else .value (.word (Core.Word.ofNatModulo 10000)))
      (secondLogged object missingGas) := by
  apply Semantics.EvalExpr.call rfl .nil
  cases missingGas <;> exact .external (by rfl) rfl (.runtime rfl)

theorem source (object : Contract.CompiledObject) (missingGas isStatic : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction code] RuntimeLogEffectsSemantics.effects
      (AccountRuntime.frameFunction code) [] (initial object missingGas isStatic)
      (result missingGas isStatic) (finalState object missingGas isStatic) := by
  cases isStatic with
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language Core.Word.maximum)) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (memory_source object missingGas true))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (static_log_source object missingGas))
        (by intro impossible; cases impossible)
  | false =>
    cases missingGas with
    | false =>
        apply Semantics.EvalFunction.body (control := .fallthrough) rfl
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (memory_source object false false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (first_log_source object false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (overwrite_source object false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (second_log_source object false))
        exact .next (by intros; intro impossible; cases impossible) (.expression rfl (gas_source object false)) .nil
    | true =>
        apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 9))) rfl
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (memory_source object true false))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (first_log_source object true))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (overwrite_source object true))
        apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
          (.expression rfl (second_log_source object true))
        exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (gas_source object true))
          (by intro impossible; cases impossible)


private theorem gas_supported : ContractLogCorrespondence.supported "gas" := by
  refine Or.inl (Or.inr ⟨.gas, rfl, ?_⟩)
  intro input present
  simp only [EnvironmentBuiltinCorrespondence.inputs, List.mem_singleton] at present
  subst input
  simp [Effects.slots, EnvironmentBuiltinCorrespondence.optionalWord]

theorem eligible : ExecutableProgram ContractLogCorrespondence.supported [AccountRuntime.frameFunction code] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8") (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log1") (Or.inr ⟨.log1, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "mstore8") (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · apply ExecutableExpression.external (name := "log0") (Or.inr ⟨.log0, rfl⟩) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · exact .external gas_supported (by rfl) (by intro _ member; cases member) _ _

theorem public_resumes (missingGas isStatic : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare program ["Logs"] (context missingGas isStatic) 64 = .ok prepared) :
    ∃ object, Contract.compileObject program ["Logs"] 64 none [] = .ok object ∧
      prepared = object.instantiate (context missingGas isStatic) ∧
      ∃ value, ContractLogCorrespondence.PublicMessageRel (context missingGas isStatic)
        (result missingGas isStatic) (finalState object missingGas isStatic).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractLogCorrespondence.prepare_resumes_exact
    (code := code) (by rfl) accepted eligible rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object missingGas isStatic)⟩

def expectedEvents : List Logs.Event := [
  ⟨Core.Word.ofNatModulo 11, [Core.Word.ofNatModulo 7], 171 :: List.replicate 32 0⟩,
  ⟨Core.Word.ofNatModulo 11, [], [205]⟩]

private def check (missingGas isStatic : Bool) : IO Unit := do
  let object ← match Contract.compileObject program ["Logs"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"log correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context missingGas isStatic)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"log correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"log correspondence: short resume completed: {reprStr outcome}")
  let resumed := Contract.resumeWithReceipt checkpoint 500000
  for receipt in [Contract.runWithReceipt prepared 500000, resumed] do
    match isStatic, missingGas, receipt.outcome with
    | false, false, .returned [] [] =>
        unless receipt.logs == expectedEvents do
          throw (IO.userError s!"log correspondence: event payload snapshot changed: {reprStr receipt.logs}")
    | false, true, .languageFailure (.word reason) =>
        unless reason == Core.Word.ofNatModulo 9 && receipt.logs.isEmpty && receipt.world.isEmpty do
          throw (IO.userError "log correspondence: failed message exported logs or world")
    | true, _, .invalid =>
        unless receipt.logs.isEmpty && receipt.world.isEmpty do
          throw (IO.userError "log correspondence: static rejection exported logs or world")
    | _, _, outcome => throw (IO.userError s!"log correspondence: incorrect outcome: {reprStr outcome}")
  match Core.runStateful 500000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair _ (.pair _ (.pair memory (.pair _ (.pair logs (.pair cursor _)))))))) _ =>
      let expected := (finalState object missingGas isStatic).external
      unless memory == Core.WordMapping.encode expected.runtime.runtime.memory.words &&
          logs == Core.WordMapping.encode expected.words && cursor == .word expected.cursor &&
          exit == .word expected.runtime.runtime.storage.exit do
        throw (IO.userError "log correspondence: internal snapshot lost earlier memory or logs")
      match Logs.decodeValues logs cursor with
      | .ok events =>
          unless events == (if isStatic then [] else expectedEvents) do
            throw (IO.userError "log correspondence: internal event snapshot differs")
      | .error error => throw (IO.userError s!"log correspondence: malformed log snapshot: {error}")
  | outcome => throw (IO.userError s!"log correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  check false false
  check true false
  check false true

end Tests.RustHullLogCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullMemoryCopyDerivations
/-! A 33-byte copy uses one full word and one byte. Its final byte comes from
an immutable source even when the first destination write overlaps that byte. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullMemoryCopyDerivations
open Solcore Solcore.Frontend.RustHull
abbrev word := Core.Word.ofNatModulo

def calldata : List UInt8 := (List.range 32).map (fun index => UInt8.ofNat (index + 1))
def calldataWord : Core.Word := word 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
def calldataWords : MemorySemantics.Entries :=
  [(word 0, calldataWord)]

def copied33 (sourceWords destinationWords : MemorySemantics.Entries) (destination source : Core.Word) :
    MemorySemantics.Entries :=
  MemoryCopySemantics.written
    (MemoryCopySemantics.written destinationWords destination (word 33)
      (MemoryCopySemantics.copiedWord sourceWords source (word 33)))
    (destination.add (word 32)) (word 1)
    (MemoryCopySemantics.copiedWord (MemoryCopySemantics.remainingSource sourceWords source (word 33))
      (source.add (word 32)) (word 1))

theorem copy33 (sourceWords destinationWords : MemorySemantics.Entries) (destination source : Core.Word) :
    MemoryCopySemantics.Copy sourceWords destination source (word 33) destinationWords
      (copied33 sourceWords destinationWords destination source) := by
  apply MemoryCopySemantics.Copy.step (by decide)
  apply MemoryCopySemantics.Copy.step (by decide)
  exact .empty _ _ _ _

def first : MemorySemantics.State := ⟨copied33 calldataWords [] (word 1) (word 0), word 64⟩
def right : MemorySemantics.State := ⟨copied33 first.words first.words (word 2) (word 1), word 64⟩
def left : MemorySemantics.State := ⟨copied33 right.words right.words (word 0) (word 2), word 64⟩

theorem from_calldata :
    MemoryCopySemantics.From calldataWords (word 1) (word 0) (word 33) {} (.value .unit) first :=
  .done (by decide) (copy33 _ _ _ _)

theorem overlap_right :
    MemoryCopySemantics.Move (word 2) (word 1) (word 33) first (.value .unit) right :=
  .done (destinationSize := word 64) (by decide) (by decide) (by decide) (by decide) (copy33 _ _ _ _)

theorem overlap_left :
    MemoryCopySemantics.Move (word 0) (word 2) (word 33) right (.value .unit) left :=
  .done (destinationSize := word 64) (by decide) (by decide) (by decide) (by decide) (copy33 _ _ _ _)

theorem destination_overflow :
    MemoryCopySemantics.Move Core.Word.maximum (word 0) (word 1) left MemorySemantics.overflow left :=
  .destinationOverflow _ (by decide)

theorem source_overflow :
    MemoryCopySemantics.Move (word 96) Core.Word.maximum (word 1) left MemorySemantics.overflow left :=
  .sourceOverflow _ (by decide) (by decide)

theorem empty_maximum :
    MemoryCopySemantics.Move Core.Word.maximum Core.Word.maximum Core.Word.zero left (.value .unit) left :=
  .done (by decide) (by decide) (by rfl) (by rfl) (.empty _ _ _ _)

theorem zero_fill : MemoryCopySemantics.readByte first.words (word 33) = Core.Word.zero := by decide +kernel
theorem right_snapshot_tail : MemoryCopySemantics.readByte right.words (word 34) = Core.Word.zero := by decide +kernel
theorem right_previous_byte : MemoryCopySemantics.readByte right.words (word 33) = word 32 := by decide +kernel
theorem left_word : MemorySemantics.readWord left.words (word 0) = calldataWord := by decide +kernel
theorem left_tail : MemoryCopySemantics.readByte left.words (word 32) = Core.Word.zero := by decide +kernel

end Tests.RustHullMemoryCopyDerivations
end

section
-- leanmerge: from Solcore.Test.RustHullMemoryCopyCorrespondence
/-! Calldata copying and both overlap directions preserve a retained source.
The independent derivation reaches public return or overflow after repeated
resumption, including an empty range at the largest address. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullMemoryCopyCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
open RustHullMemoryCopyDerivations (calldata calldataWords first right left)

inductive Scenario where | returned | empty | destinationOverflow | sourceOverflow
  deriving DecidableEq, Repr

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (arguments : List Expr) : Expr := ⟨.unit, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
def calldataCopy : Expr := call "calldatacopy" [word "1", word "0", word "33"]
def copyRight : Expr := call "mcopy" [word "2", word "1", word "33"]
def copyLeft : Expr := call "mcopy" [word "0", word "2", word "33"]
def returnBytes : Expr := call "return" [word "0", word "33"]
def lastCopy : Scenario → Expr
  | .returned => call "mcopy" [word "0", word "0", word "0"]
  | .empty => call "mcopy" [word maximum, word maximum, word "0"]
  | .destinationOverflow => call "mcopy" [word maximum, word "0", word "1"]
  | .sourceOverflow => call "mcopy" [word "96", word maximum, word "1"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression calldataCopy, expression copyRight, expression copyLeft,
    expression (lastCopy scenario), expression returnBytes]
  functions := []
}
def program (scenario : Scenario) : Program := {
  entryPoints := [], functions := [], objects := [.object "Copy" (code scenario) []]
}
def context : Contract.Context := {calldata := calldata}
def initial (object : Contract.CompiledObject) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  ⟨[], ContractCopyCorrespondence.contextInitialState object (Contract.normalizeContext context)⟩
def copied (object : Contract.CompiledObject) (memory : MemorySemantics.State) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  ⟨[], RuntimeCopyEffectsSemantics.withMemory (initial object).external memory⟩
def succeeds : Scenario → Bool
  | .returned | .empty => true
  | _ => false

def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeCopyEffectsSemantics.State :=
  if succeeds scenario then
    ⟨[], RuntimeFullEffectsSemantics.withRuntime (copied object left).external
      (TerminationSemantics.terminate (copied object left).external.runtime.runtime 1
        Core.Word.zero (Core.Word.ofNatModulo 33)).2⟩
  else copied object left

def reason (scenario : Scenario) : Core.Word :=
  if succeeds scenario then Core.Word.maximum else Core.Word.ofNatModulo 6

def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem calldata_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] calldataCopy
      (initial object) (.value .unit) (copied object first) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.calldata RustHullMemoryCopyDerivations.from_calldata))

private theorem right_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] copyRight
      (copied object first) (.value .unit) (copied object right) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "2") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.overlap_right))

private theorem left_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] copyLeft
      (copied object right) (.value .unit) (copied object left) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "33") rfl) .nil))
  · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.overlap_left))

private theorem last_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] (lastCopy scenario)
      (copied object left)
      (if succeeds scenario then .value .unit else MemorySemantics.overflow) (copied object left) := by
  cases scenario
  case returned =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move (.done (by rfl) (by rfl) (by rfl) (by rfl) (.empty _ _ _ _))))
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.empty_maximum))
  case destinationOverflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.destination_overflow))
  case sourceOverflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "96") rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.move RustHullMemoryCopyDerivations.source_overflow))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario)
    (successful : succeeds scenario = true) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects [] returnBytes
      (copied object left) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, ↓reduceIte]
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "33") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.termination rfl))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] RuntimeCopyEffectsSemantics.effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (calldata_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (right_source object scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (left_source object scenario))
  cases successful : succeeds scenario with
  | true =>
      have last := last_source object scenario
      simp only [successful, ↓reduceIte] at last
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl last)
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
        (by intro impossible; cases impossible)
  | false =>
      have last := last_source object scenario
      simp only [successful, Bool.false_eq_true, ↓reduceIte] at last
      simp only [reason, finalState, successful, Bool.false_eq_true, ↓reduceIte]
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl last)
        (by intro impossible; cases impossible)

private theorem words_eligible {name : String} {texts : List String} (scenario : Scenario)
    (available : ContractCopyCorrespondence.supported name)
    (absent : [AccountRuntime.frameFunction (code scenario)].find? (·.name == name) = none) :
    ExecutableExpression ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)]
      (call name (texts.map word)) := by
  apply ExecutableExpression.external available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

private theorem last_eligible (scenario : Scenario) :
    ExecutableExpression ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (lastCopy scenario) := by
  cases scenario
  case returned => exact words_eligible (texts := ["0", "0", "0"]) .returned (Or.inr ⟨.move, rfl⟩) rfl
  case empty => exact words_eligible (texts := [maximum, maximum, "0"]) .empty (Or.inr ⟨.move, rfl⟩) rfl
  case destinationOverflow => exact words_eligible (texts := [maximum, "0", "1"]) .destinationOverflow (Or.inr ⟨.move, rfl⟩) rfl
  case sourceOverflow => exact words_eligible (texts := ["96", maximum, "1"]) .sourceOverflow (Or.inr ⟨.move, rfl⟩) rfl

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractCopyCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact words_eligible (texts := ["1", "0", "33"]) scenario (Or.inr ⟨.calldata, rfl⟩) rfl
  · exact words_eligible (texts := ["2", "1", "33"]) scenario (Or.inr ⟨.move, rfl⟩) rfl
  · exact words_eligible (texts := ["0", "2", "33"]) scenario (Or.inr ⟨.move, rfl⟩) rfl
  · exact last_eligible scenario
  · exact words_eligible (texts := ["0", "33"]) scenario (Or.inl (Or.inr ⟨.returned, rfl⟩)) rfl

theorem public_resumes (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Copy"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Copy"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractCopyCorrespondence.PublicMessageRel context (result scenario) (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractCopyCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Copy"] 64 with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"copy correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"copy correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 17).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"copy correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 1000000
  match succeeds scenario, receipt.outcome with
  | true, .returned bytes storage =>
      unless bytes == calldata ++ [0] && storage.isEmpty do
        throw (IO.userError "copy correspondence: copied bytes or empty storage differ")
  | false, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 && receipt.world.isEmpty do
        throw (IO.userError "copy correspondence: overflow reason/export differs")
  | _, outcome => throw (IO.userError s!"copy correspondence: incorrect outcome: {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair count (.pair memory _))))) _ =>
      let state := (finalState object scenario).external.runtime.runtime
      unless memory == Core.WordMapping.encode left.words && exit == .word state.storage.exit &&
          offset == .word state.storage.returnOffset && count == .word state.storage.returnSize do
        throw (IO.userError "copy correspondence: Core snapshot differs from independent copy")
  | outcome => throw (IO.userError s!"copy correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.returned, .empty, .destinationOverflow, .sourceOverflow] do check scenario

end Tests.RustHullMemoryCopyCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullMemoryCorrespondence
/-! Independent memory computation and actual public contract execution agree
on unaligned word access and on a language fault after a completed write. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.RustHullMemoryCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (name : String) (type : Ty) (arguments : List Expr) : Expr :=
  ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def write : Expr := call "mstore" .unit [word "1", word "171"]
def read : Expr := call "mload" .word [word "1"]
def overflow : Expr := call "mload" .word [word "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"]
def code (fault : Bool) : CodeBlock := {
  stmts := [expression write, expression (if fault then overflow else read)]
  functions := []
}
def program (fault : Bool) : Program := {
  entryPoints := [], functions := [], objects := [.object "Memory" (code fault) []]
}
def initial : Semantics.State MemorySemantics.State := ⟨[], {}⟩
def written : Semantics.State MemorySemantics.State :=
  ⟨[], (MemorySemantics.mstore {} (Core.Word.ofNatModulo 1) (Core.Word.ofNatModulo 171)).2⟩

private theorem write_source (fault : Bool) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code fault)] MemorySemantics.effects [] write initial
      (.value .unit) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl rfl

private theorem read_source :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code false)] MemorySemantics.effects [] read written
      (.value (.word (Core.Word.ofNatModulo 171))) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) .nil
  · exact .external (by rfl) rfl rfl

private theorem overflow_source :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code true)] MemorySemantics.effects [] overflow written
      (.fault (.language (Core.Word.ofNatModulo 6))) written := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff") rfl) .nil
  · exact .external (by rfl) rfl rfl

theorem source (fault : Bool) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code fault)] MemorySemantics.effects
      (AccountRuntime.frameFunction (code fault)) [] initial
      (if fault then .fault (.language (Core.Word.ofNatModulo 6)) else .value .unit) written := by
  cases fault with
  | false =>
      apply Semantics.EvalFunction.body (control := .fallthrough) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (write_source false))
      exact .next (by intros; intro impossible; cases impossible) (.expression rfl read_source) .nil
  | true =>
      apply Semantics.EvalFunction.body (control := .fault (.language (Core.Word.ofNatModulo 6))) rfl
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
        (.expression rfl (write_source true))
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl overflow_source)
        (by intro impossible; cases impossible)

theorem eligible (fault : Bool) :
    ExecutableProgram MemoryEffectCorrespondence.supported [AccountRuntime.frameFunction (code fault)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") ⟨.store, rfl⟩ (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · cases fault <;>
      apply ExecutableExpression.external (name := "mload") ⟨.load, rfl⟩ (by rfl)
    all_goals
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst argument
      exact .word _ _ _

/-- The concrete independent derivations reach every actual public checkpoint
chain, including a language fault after the completed unaligned write. -/
theorem public_resumes (fault : Bool) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program fault) ["Memory"] {} 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program fault) ["Memory"] 64 none [] = .ok object ∧
      prepared = object.instantiate {} ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
        (last = Contract.finish limit
          (ContractMemoryCorrespondence.publicMessageValue object {}
            (if fault then .fault (.language (Core.Word.ofNatModulo 6)) else .value .unit)
            written.external) ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractMemoryCorrespondence.prepare_resumes_exact
    (code := code fault) (by rfl) accepted (eligible fault) rfl (source fault)

private def check (fault : Bool) : IO Unit := do
  let prepared ← match Contract.prepare (program fault) ["Memory"] {} 64 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"memory correspondence: preparation failed: {reprStr error}")
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"memory correspondence: zero fuel completed: {reprStr result}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 11).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | result => throw (IO.userError s!"memory correspondence: short resume completed: {reprStr result}")
  let receipt := Contract.resumeWithReceipt checkpoint 300000
  match fault, receipt.outcome with
  | false, .returned [] [] => pure ()
  | true, .languageFailure (.word reason) =>
      unless reason == Core.Word.ofNatModulo 6 do
        throw (IO.userError "memory correspondence: incorrect fault reason")
  | _, result => throw (IO.userError s!"memory correspondence: incorrect public outcome: {reprStr result}")
  match Core.runStateful 300000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair _ (.pair _ (.pair _ (.pair memory _))))) _ =>
      unless memory == Core.WordMapping.encode written.external.words do
        throw (IO.userError "memory correspondence: write was lost before snapshot or fault")
  | result => throw (IO.userError s!"memory correspondence: Core execution failed: {reprStr result}")

def run : IO Unit := do
  check false
  check true

end Tests.RustHullMemoryCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullMemorySnapshot
set_option autoImplicit false
namespace Tests.RustHullMemorySnapshot
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Solcore.Core.Expr := .word (word value)
private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong nil constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong cons constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid packed snapshot"
private def decoded : StatefulRunResult → IO WordMapping.Entries
  | .done (.inRight _ value) _ => match entries value with
      | .ok result => pure result
      | .error error => throw (IO.userError error)
  | other => throw (IO.userError s!"snapshot failed: {reprStr other}")
private def program (mapping : WordMapping.Entries) (offset length : Nat) : Program := {
  dataDefinitions := MemorySnapshot.definitions
  resultType := LanguageResult.resultType WordMapping.type
  body := MemorySnapshot.extract (WordMapping.literal mapping) (number offset) (number length)
}
private def execute (label : String) (mapping : WordMapping.Entries) (offset length : Nat)
    (fuel : Nat := 1000000) : IO WordMapping.Entries := do
  let compiled := program mapping offset length
  require compiled.check s!"{label}: ill-typed snapshot"
  let actual ← decoded (compiled.runStateful fuel)
  for index in List.range (length + 32) do
    let expected := if index < length && offset + index < wordModulus then
      Memory.lookupByte mapping (word (offset + index)) else Word.zero
    require (Memory.lookupByte actual (word index) == expected) s!"{label}: wrong byte at {index}"
  pure actual

private def rangeTests : IO Unit := do
  let mapping := Memory.packBytes ((List.range 147).map fun index => UInt8.ofNat (index * 17 + 3))
  for offset in [0, 32, 96, 2048] do
    for length in [0, 1, 31, 32, 33, 63, 64, 65] do
      discard (execute s!"aligned {offset}/{length}" mapping offset length)
  for offset in [1, 31, 33, 127] do
    for length in [0, 1, 31, 32, 33, 65] do
      discard (execute s!"unaligned {offset}/{length}" mapping offset length)
  let duplicate := [(word 9, word 55), (word 1, Word.zero), (word 1, Word.maximum),
    (word 2, Word.maximum), (word 0, word 8), (word 2, word 1), (word 3, word 7)]
  let actual ← execute "duplicates retain first-match order" duplicate 32 33
  let mask := (Word.maximum.shiftRight (word 248)).shiftLeft (word 248)
  require (actual == [(word 0, Word.zero), (word 0, Word.maximum), (word 1, mask), (word 1, Word.zero)])
    "aligned filter changed duplicate order or retained unrelated entries"
  let complete ← execute "full words are unchanged" duplicate 32 64
  require (complete == [(word 0, Word.zero), (word 0, Word.maximum),
    (word 1, Word.maximum), (word 1, word 1)]) "full-word snapshot changed packed values"

private def boundaryTests : IO Unit := do
  let last := (wordModulus - 1) / 32
  let mapping := [(word last, Word.maximum), (word (last + 1), Word.maximum),
    (Word.zero, Word.maximum), (Word.maximum, Word.maximum)]
  discard (execute "aligned source cannot wrap" mapping (wordModulus - 32) 64)
  discard (execute "unaligned source cannot wrap" mapping (wordModulus - 4) 12)
  let empty ← execute "zero length ignores maximum offset" mapping (wordModulus - 1) 0
  require empty.isEmpty "zero length retained source entries"
  for length in [wordModulus - 31, wordModulus - 1] do
    let compiled := program mapping 0 length
    require compiled.check "overflow fixture is ill-typed"
    match compiled.runStateful 10000 with
    | .done (.inLeft _ (.word reason)) _ => require (reason == Memory.overflowReason) "wrong overflow reason"
    | other => throw (IO.userError s!"oversized destination accepted: {reprStr other}")
  let largest := program [] 0 (wordModulus - 32)
  require largest.check "largest representable snapshot is ill-typed"
  require (← decoded (largest.runStateful 10000)).isEmpty "empty largest snapshot changed contents"

private def onceAndResumeTests : IO Unit := do
  let mapping := Memory.packBytes ((List.range 65).map UInt8.ofNat)
  let tick (value : Solcore.Core.Expr) := Solcore.Core.Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (value.weakenAt 0)
  let once : Program := {
    dataDefinitions := MemorySnapshot.definitions
    resultType := .product (LanguageResult.resultType WordMapping.type) .word
    body := .letE (.newCell .word (number 0))
      (.letE (MemorySnapshot.extract (tick (WordMapping.literal mapping)) (tick (number 32)) (tick (number 33)))
        (.pair (.var 0) (.loadCell (.var 1))))
  }
  require once.check "once-only inputs fixture is ill-typed"
  match once.runStateful 100000 with
  | .done (.pair (.inRight _ _) (.word count)) _ => require (count == word 3) "snapshot repeated an input"
  | other => throw (IO.userError s!"once-only inputs failed: {reprStr other}")
  let large := (List.range 320).map fun index => (word index, word (index + 1))
  let compiled := program large 0 10240
  require compiled.check "linear snapshot fixture is ill-typed"
  let expected := WordMapping.encode large
  match compiled.runStateful 100000 with
  | .done (.inRight _ value) _ => require (value == expected) "linear snapshot changed values"
  | other => throw (IO.userError s!"10 KiB aligned snapshot exceeded linear fuel budget: {reprStr other}")
  let rec resume : Nat → State → IO StatefulRunResult
    | 0, _ => throw (IO.userError "snapshot repeated-resume budget exhausted")
    | attempts + 1, state => match runStateful 113 state with
      | .outOfFuel next => resume attempts next
      | result => pure result
  match compiled.runStateful 1 with
  | .outOfFuel checkpoint =>
      let actual ← decoded (← resume 1000 checkpoint)
      require (actual == large) "resumed snapshot changed entry order or values"
  | _ => throw (IO.userError "snapshot fixture did not suspend")

def run : IO Unit := do
  rangeTests
  boundaryTests
  onceAndResumeTests
  IO.println "Rust Hull memory snapshot tests passed"
end Tests.RustHullMemorySnapshot
end

section
-- leanmerge: from Solcore.Test.RustHullPrecompileCorrespondence
/-! Calls to the identity precompile reach the actual dispatcher and precompile
code. The child-free scenarios cover a funded copy, insufficient forwarded gas,
a value transfer to the precompiled account and a static call, followed by the
caller's output copy and public resumption. CALLCODE and DELEGATECALL reach the
same precompile through the call-mode theorem. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullPrecompileCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | identity | underfunded | transfer | staticCall
  deriving DecidableEq, Repr
private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def context : Contract.Context := {balance := w 10, completeWorld := true}
def operation (scenario : Scenario) : RuntimeCallEffectsSemantics.Operation :=
  if scenario = .staticCall then .staticCall else .ordinary
def gasText (scenario : Scenario) : String := if scenario = .underfunded then "17" else "100"
def gas (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 17 else w 100
def valueText (scenario : Scenario) : String := if scenario = .transfer then "3" else "0"
def value (scenario : Scenario) : Core.Word := if scenario = .transfer then w 3 else w 0
def seed : Expr := call .unit "mstore8" [word "1", word "171"]
def invoked (scenario : Scenario) : Expr :=
  let tail := [word "1", word "1", word "3", word "2"]
  if scenario = .staticCall then call .word "staticcall" ([word (gasText scenario), word "4"] ++ tail)
  else call .word "call" ([word (gasText scenario), word "4", word (valueText scenario)] ++ tail)
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def returned : Expr := call .unit "return" [word "1", word "3"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Precompile" (code scenario) []]}
abbrev SourceState := Semantics.State RuntimeCallEffectsSemantics.State

def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ⟨⟨ContractCodeCorrespondence.contextInitialState none object (Contract.normalizeContext context), []⟩, w 0⟩⟩
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {state.external.runtime.runtime.runtime.runtime.runtime with memory := memory})}⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) : SourceState := withMemory (initial object) seeded

/-- The caller's one-byte input snapshot and the identity output copied from it. -/
def input : MemorySemantics.State :=
  ⟨MemoryCopySemantics.written [] (w 0) (w 1) (MemoryCopySemantics.copiedWord seeded.words (w 1) (w 1)), w 32⟩
def output : MemorySemantics.Entries :=
  MemoryCopySemantics.written [] (w 0) (w 1) (MemoryCopySemantics.copiedWord input.words (w 0) (w 1))
def response (scenario : Scenario) : AccountCallSemantics.Response :=
  if scenario = .underfunded then AccountCallSemantics.emptyResponse false else ⟨true, output, w 1⟩
def status (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 0 else w 1
def copiedMemory (scenario : Scenario) : MemorySemantics.State :=
  if scenario = .underfunded then ⟨seeded.words, w 32⟩
  else ⟨MemoryCopySemantics.written seeded.words (w 3) (w 1) (MemoryCopySemantics.copiedWord output (w 0) (w 1)), w 32⟩
def sharedAfter (object : Contract.CompiledObject) (scenario : Scenario) : AccountCallSemantics.Shared :=
  let old := RuntimeCallEffectsSemantics.shared (memoryWritten object).external
  if scenario = .transfer then {old with balances := [(w 0, w 7), (w 4, w 3)]} else old
def nextTransport (scenario : Scenario) : CallTransportSemantics.State :=
  ⟨copiedMemory scenario, (response scenario).data, (response scenario).size⟩
def afterCall (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (memoryWritten object).external (nextTransport scenario)
    (sharedAfter object scenario)⟩
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterCall object scenario) (MemorySemantics.mstore8 (copiedMemory scenario) (w 2) (status scenario)).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 3)).2)}⟩
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] seed
      (initial object) (.value .unit) (memoryWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem input_copied :
    MemoryCopySemantics.From seeded.words (w 0) (w 1) (w 1) {} (.value .unit) input := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) input.words input.words
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

/-- The independent identity meaning: a byte copy of the complete input. -/
private theorem identity_copied :
    MemoryCopySemantics.Copy input.words Core.Word.zero Core.Word.zero (w 1) [] output := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) output output
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem output_copied :
    MemoryCopySemantics.Copy output (w 3) Core.Word.zero (w 1) seeded.words (copiedMemory .identity).words := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  change MemoryCopySemantics.Copy _ _ _ ((w 1).sub (w 1)) (copiedMemory .identity).words (copiedMemory .identity).words
  rw [show (w 1).sub (w 1) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem transfer_balances :
    AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)] = .ok [(w 0, w 7), (w 4, w 3)] := by
  have computed : (AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)]).toOption =
      some [(w 0, w 7), (w 4, w 3)] := by decide +kernel
  cases found : AccountCallSemantics.transfer (w 0) (w 4) (w 3) [(w 0, w 10)] with
  | error error => simp [found, Except.toOption] at computed
  | ok entries => exact congrArg Except.ok (Option.some.inj (by simpa only [found, Except.toOption] using computed))

private theorem target_masked : (w 4).bitAnd (w (2 ^ 160 - 1)) = w 4 := by decide +kernel

private theorem invoked_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) (operation scenario)
      (gas scenario) (w 4) (value scenario) (w 1) (w 1) (w 3) (w 2)
      (memoryWritten object).external (.value (.word (status scenario))) (afterCall object scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked
  · cases scenario
    · exact .inr (.inl rfl)
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
    · exact .inl rfl
  · intros ordinary nonzero
    cases scenario <;> first | exact False.elim (nonzero rfl) | decide +kernel
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 3) (w 2) = some (w 32)
    decide +kernel
  cases scenario
  case identity =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .identity) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied
  case underfunded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .underfunded) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.refused
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identityUnderfunded (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change (w 17).val < AccountCallSemantics.linearCost 15 3 (w 1)
          decide
      · rfl
    · exact .done rfl (.empty _ _ _ _)
  case transfer =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .transfer) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded (transferred := sharedAfter object .transfer)
      · exact .inr (by change ¬w 3 > w 10; decide +kernel)
      · dsimp only [AccountCallSemantics.transferFor]
        simp only [show (AccountCallSemantics.Mode.ordinary == .ordinary) = true from rfl, ↓reduceIte]
        have moved : AccountCallSemantics.transfer (w 0) ((w 4).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)] =
            .ok [(w 0, w 7), (w 4, w 3)] := by
          rw [target_masked]
          exact transfer_balances
        change Except.map _ (AccountCallSemantics.transfer (w 0) ((w 4).bitAnd (w (2 ^ 160 - 1))) (w 3) [(w 0, w 10)]) = _
        rw [moved]
        rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ ((w 100).add (w 2300)).val
          decide +kernel
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied
  case staticCall =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .staticCall) (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · apply AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
      · exact .inr (by change ¬w 0 > w 10; decide +kernel)
      · rfl
      · apply AccountCallSemantics.Run.precompile
        apply AccountCallSemantics.Precompile.identity (size := w 32)
        · exact target_masked
        · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
        · exact identity_copied
      · rfl
    · apply MemoryCopySemantics.From.done (size := w 32)
      · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
        decide +kernel
      · exact output_copied

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (invoked scenario)
      (memoryWritten object) (.value (.word (status scenario))) (afterCall object scenario) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "17") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))))
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil))))))
    | exact .external (by rfl) rfl (.call (invoked_source object .identity))
    | exact .external (by rfl) rfl (.call (invoked_source object .underfunded))
    | exact .external (by rfl) rfl (.call (invoked_source object .transfer))
    | exact .external (by rfl) rfl (.staticCall (invoked_source object .staticCall))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] (stored scenario)
      (memoryWritten object) (.value .unit) (afterStore object scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (call_source object scenario) .nil))
  cases scenario <;>
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none) [] returned
      (afterStore object scenario) result (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil)
  · cases scenario <;>
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] (RuntimeCallEffectsSemantics.effects none)
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object _))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (store_source object _))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "call", "staticcall", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (arguments : List String) (available : supported name)
    (absent : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (arguments.map word)) := by
  apply ExecutableExpression.external (name := name) available absent
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "staticcall" ["100", "4", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "4", "0", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["17", "4", "0", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["100", "4", "3", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "3"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported false name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩))))))))
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩)))))

/-- Public consumer: actual compilation success is the only premise besides the
independent source derivation constructed above. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Precompile"] 64 none [] = .ok object) :
    ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallCorrespondence.compileObject_resumes_exact (code := code scenario) (by rfl) accepted
    (eligible scenario names_supported) context rfl (source object scenario)

theorem public_prepared (scenario : Scenario) {prepared : Contract.Prepared}
    (accepted : Contract.prepare (program scenario) ["Precompile"] context 64 = .ok prepared) :
    ∃ object, Contract.compileObject (program scenario) ["Precompile"] 64 none [] = .ok object ∧
      prepared = object.instantiate context ∧
      ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object scenario).external value ∧
        ∃ required, ∀ initialFuel additional limit last,
          Contract.ReceiptResumes limit (Contract.runWithReceipt prepared initialFuel limit) additional last →
          (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
          ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨object, compiled, preparedEq, consume⟩ := ContractCallCorrespondence.prepare_resumes_exact
    (code := code scenario) (by rfl) accepted (eligible scenario names_supported) rfl
  exact ⟨object, compiled, preparedEq, consume _ _ (source object scenario)⟩

private def expectedBytes (scenario : Scenario) : List UInt8 :=
  if scenario = .underfunded then [171, 0, 0] else [171, 1, 171]
private def expectedBalances (scenario : Scenario) : Core.WordMapping.Entries :=
  if scenario = .transfer then [(w 0, w 7), (w 4, w 3)] else [(w 0, w 10)]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Precompile"] 64 none [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"precompile correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile correspondence: short resume completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == expectedBalances scenario do
          throw (IO.userError s!"precompile correspondence: wrong result for {reprStr scenario}: {reprStr receipt}")
    | outcome => throw (IO.userError s!"precompile correspondence: expected return for {reprStr scenario}: {reprStr outcome}")
  match Core.runStateful 1000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair length (.pair memory (.pair _ (.pair _ (.pair _ (.pair balances _))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words &&
          balances == Core.WordMapping.encode (expectedBalances scenario) && exit == .word runtime.storage.exit &&
          offset == .word runtime.storage.returnOffset && length == .word runtime.storage.returnSize do
        throw (IO.userError s!"precompile correspondence: internal snapshot mismatch for {reprStr scenario}")
  | outcome => throw (IO.userError s!"precompile correspondence: Core failed: {reprStr outcome}")

namespace Modes

/-- CALLCODE with value and DELEGATECALL select the precompile by the requested
target. Neither moves balances; CALLCODE still checks the caller's funds. -/
inductive Scenario where
  | callCode | delegated
  deriving DecidableEq, Repr
def rootBytes : List UInt8 := [0]
def context : Contract.Context := {caller := w 55, value := w 7, balance := w 10, completeWorld := true}
def operation : Scenario → RuntimeCallModeSemantics.Operation
  | .callCode => .callCode | .delegated => .delegateCall
def invoked : Scenario → Expr
  | .callCode => call .word "callcode" [word "100", word "4", word "5", word "1", word "1", word "3", word "2"]
  | .delegated => call .word "delegatecall" [word "100", word "4", word "1", word "1", word "3", word "2"]
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Precompile" (code scenario) []]}
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩
def memoryWritten (object : Contract.CompiledObject) : SourceState := withMemory (initial object) seeded
def value (object : Contract.CompiledObject) : Scenario → Core.Word
  | .callCode => w 5
  | .delegated => (RuntimeCallModeSemantics.observations (memoryWritten object).external).direct .callvalue
def afterCall (object : Contract.CompiledObject) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (memoryWritten object).external (nextTransport .identity)
    (RuntimeCallEffectsSemantics.shared (memoryWritten object).external)⟩
def afterStore (object : Contract.CompiledObject) : SourceState :=
  withMemory (afterCall object) (MemorySemantics.mstore8 (copiedMemory .identity) (w 2) (w 1)).2
def finalState (object : Contract.CompiledObject) : SourceState :=
  let state := (afterStore object).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 3)).2)}⟩

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] seed
      (initial object) (.value .unit) (memoryWritten object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem invoked_source (object : Contract.CompiledObject) (scenario : Scenario) :
    RuntimeCallModeSemantics.Call (ChildFrameModeSemantics.Children [] (ChildFrameModeSemantics.effectsAt [] {} 0))
      (operation scenario) (w 100) (w 4) (value object scenario) (w 1) (w 1) (w 3) (w 2)
      (memoryWritten object).external (.value (.word (w 1))) (afterCall object).external := by
  apply RuntimeCallModeSemantics.Call.invoked
  · exact .inl (by cases scenario <;> intro impossible <;> cases impossible)
  · intro stipend nonzero
    cases scenario
    · change ¬w 100 > w (Core.wordModulus - 2301)
      decide +kernel
    · cases stipend
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 32)
  · change MemorySemantics.touchSize? seeded.size (w 1) (w 1) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 3) (w 2) = some (w 32)
    decide +kernel
  apply CallTransportSemantics.Dispatch.returned (input := input) (response := response .identity) (result := .value .unit)
  · change ¬w 0 > w 1023
    decide +kernel
  · exact input_copied
  · rfl
  · apply AccountCallSemantics.Dispatch.succeeded
      (transferred := RuntimeCallEffectsSemantics.shared (memoryWritten object).external)
    · cases scenario
      · exact .inr (by change ¬w 5 > w 10; decide +kernel)
      · exact .inl rfl
    · cases scenario <;> rfl
    · apply AccountCallSemantics.Run.precompile
      apply AccountCallSemantics.Precompile.identity (size := w 32)
      · exact target_masked
      · change MemorySemantics.touchSize? Core.Word.zero Core.Word.zero (w 1) = some (w 32)
        decide +kernel
      · cases scenario
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ ((w 100).add (w 2300)).val
          decide +kernel
        · change AccountCallSemantics.linearCost 15 3 (w 1) ≤ (w 100).val
          decide
      · exact identity_copied
    · rfl
  · apply MemoryCopySemantics.From.done (size := w 32)
    · change MemorySemantics.touchSize? (w 32) (w 3) (w 1) = some (w 32)
      decide +kernel
    · exact output_copied

private theorem call_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] (invoked scenario)
      (memoryWritten object) (.value (.word (w 1))) (afterCall object) := by
  cases scenario <;> apply Semantics.EvalExpr.call rfl
  case callCode.argumentsEvaluated =>
    exact .cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "5") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil))))))
  case callCode.called => exact .external (by rfl) rfl (.callCode (invoked_source object .callCode))
  case delegated.argumentsEvaluated =>
    exact .cons (.word (text := "100") rfl) (.cons (.word (text := "4") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "2") rfl) .nil)))))
  case delegated.called => exact .external (by rfl) rfl (.delegateCall (invoked_source object .delegated))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] (stored scenario)
      (memoryWritten object) (.value .unit) (afterStore object) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "2") rfl) (.cons (call_source object scenario) .nil))
  exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] effects [] returned
      (afterStore object) result (finalState object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] effects
      (AccountRuntime.frameFunction (code scenario)) [] (initial object) result (finalState object) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object _))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (store_source object _))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object _))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "callcode", "delegatecall", "return"]

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "callcode" ["100", "4", "5", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "delegatecall" ["100", "4", "1", "1", "3", "2"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "3"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl rfl))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem: the empty catalog has no
selected child and no initial code links. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Precompile"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result (finalState object).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) context rfl (empty_links object)
    (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Precompile"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"precompile mode correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"precompile mode correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == [171, 1, 171] && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == [(w 0, w 10)] do
          throw (IO.userError s!"precompile mode correspondence: wrong result for {reprStr scenario}: {reprStr receipt}")
    | outcome => throw (IO.userError s!"precompile mode correspondence: expected return for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.callCode, .delegated] do
    check scenario

end Modes

namespace Digest

/-- The digest precompiles: SHA-256 at address 2 and RIPEMD-160 at address 3. -/
inductive Algorithm where
  | sha256 | ripemd160
  deriving DecidableEq, Repr

/-- "abc" from caller memory, digested and copied back into caller memory. The
underfunded scenario forwards one gas unit less than the charge for three
bytes: 72 for SHA-256 and 720 for RIPEMD-160. -/
inductive Scenario where
  | funded | underfunded
  deriving DecidableEq, Repr
def address : Algorithm → Nat | .sha256 => 2 | .ripemd160 => 3
def addressText : Algorithm → String | .sha256 => "2" | .ripemd160 => "3"
def gasText : Algorithm → Scenario → String
  | .sha256, .funded => "100" | .sha256, .underfunded => "71"
  | .ripemd160, .funded => "1000" | .ripemd160, .underfunded => "719"
def gas : Algorithm → Scenario → Core.Word
  | .sha256, .funded => w 100 | .sha256, .underfunded => w 71
  | .ripemd160, .funded => w 1000 | .ripemd160, .underfunded => w 719
def seeds : List Expr := [call .unit "mstore8" [word "0", word "97"], call .unit "mstore8" [word "1", word "98"],
  call .unit "mstore8" [word "2", word "99"]]
def invoked (algorithm : Algorithm) (scenario : Scenario) : Expr :=
  call .word "call" [word (gasText algorithm scenario), word (addressText algorithm), word "0", word "0", word "3",
    word "32", word "32"]
def stored (algorithm : Algorithm) (scenario : Scenario) : Expr :=
  call .unit "mstore8" [word "64", invoked algorithm scenario]
def returned : Expr := call .unit "return" [word "32", word "33"]
def code (algorithm : Algorithm) (scenario : Scenario) : CodeBlock := {
  stmts := seeds.map expression ++ [expression (stored algorithm scenario), expression returned], functions := []}
def program (algorithm : Algorithm) (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Digest" (code algorithm scenario) []]}

def first : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 0) (w 97)).2
def second : MemorySemantics.State := (MemorySemantics.mstore8 first (w 1) (w 98)).2
def third : MemorySemantics.State := (MemorySemantics.mstore8 second (w 2) (w 99)).2
def afterThird (object : Contract.CompiledObject) : SourceState := withMemory (initial object) third

/-- The three-byte input snapshot copied by the caller. -/
def input : MemorySemantics.State :=
  ⟨MemoryCopySemantics.written (MemoryCopySemantics.written (MemoryCopySemantics.written [] (w 0) (w 3)
      (MemoryCopySemantics.copiedWord third.words (w 0) (w 3))) (w 1) (w 2)
      (MemoryCopySemantics.copiedWord third.words (w 1) (w 2))) (w 2) (w 1)
      (MemoryCopySemantics.copiedWord third.words (w 2) (w 1)), w 32⟩
/-- The independent digest of the snapshot. -/
def digest : Algorithm → Core.Word
  | .sha256 => Sha256Semantics.digest (Sha256Semantics.compress Sha256Semantics.initial
      (Sha256Semantics.readBlock input.words Core.Word.zero (w 3) (Sha256Semantics.bitLength (w 3)) false))
  | .ripemd160 => Ripemd160Semantics.digest (Ripemd160Semantics.compress Ripemd160Semantics.initial
      (Ripemd160Semantics.readBlock input.words Core.Word.zero (w 3) (Ripemd160Semantics.bitLength (w 3)) false))
def response (algorithm : Algorithm) (scenario : Scenario) : AccountCallSemantics.Response :=
  if scenario = .underfunded then AccountCallSemantics.emptyResponse false
  else ⟨true, [(Core.Word.zero, digest algorithm)], w 32⟩
def status (scenario : Scenario) : Core.Word := if scenario = .underfunded then w 0 else w 1
def copiedMemory (algorithm : Algorithm) (scenario : Scenario) : MemorySemantics.State :=
  if scenario = .underfunded then ⟨third.words, w 64⟩
  else ⟨MemoryCopySemantics.written third.words (w 32) (w 32)
    (MemoryCopySemantics.copiedWord [(Core.Word.zero, digest algorithm)] (w 0) (w 32)), w 64⟩
def nextTransport (algorithm : Algorithm) (scenario : Scenario) : CallTransportSemantics.State :=
  ⟨copiedMemory algorithm scenario, (response algorithm scenario).data, (response algorithm scenario).size⟩
def afterCall (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  ⟨[], RuntimeCallEffectsSemantics.withTransport (afterThird object).external (nextTransport algorithm scenario)
    (RuntimeCallEffectsSemantics.shared (afterThird object).external)⟩
def afterStore (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  withMemory (afterCall object algorithm scenario)
    (MemorySemantics.mstore8 (copiedMemory algorithm scenario) (w 64) (status scenario)).2
def finalState (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) : SourceState :=
  let state := (afterStore object algorithm scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 32) (w 33)).2)}⟩

private theorem first_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "0", word "97"]) (initial object) (.value .unit) (withMemory (initial object) first) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "97") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem second_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "1", word "98"]) (withMemory (initial object) first) (.value .unit)
      (withMemory (initial object) second) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "98") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem third_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (call .unit "mstore8" [word "2", word "99"]) (withMemory (initial object) second) (.value .unit)
      (afterThird object) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "2") rfl) (.cons (.word (text := "99") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem input_copied :
    MemoryCopySemantics.From third.words (w 0) (w 0) (w 3) {} (.value .unit) input := by
  apply MemoryCopySemantics.From.done (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  rw [show (((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3)))).sub
      (Core.Word.ofNatModulo (MemoryCopySemantics.width ((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3))))))).sub
      (Core.Word.ofNatModulo (MemoryCopySemantics.width (((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3)))).sub
        (Core.Word.ofNatModulo (MemoryCopySemantics.width ((w 3).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 3))))))))) =
      Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem output_copied (algorithm : Algorithm) :
    MemoryCopySemantics.Copy [(Core.Word.zero, digest algorithm)] (w 32) Core.Word.zero (w 32) third.words
      (copiedMemory algorithm .funded).words := by
  apply MemoryCopySemantics.Copy.step (by decide +kernel)
  rw [show (w 32).sub (Core.Word.ofNatModulo (MemoryCopySemantics.width (w 32))) = Core.Word.zero from by decide +kernel]
  exact .empty _ _ _ _

private theorem target_masked (algorithm : Algorithm) :
    (w (address algorithm)).bitAnd (w (2 ^ 160 - 1)) = w (address algorithm) := by
  cases algorithm <;> decide +kernel

private theorem precompile_source (algorithm : Algorithm) (scenario : Scenario)
    (request : AccountCallSemantics.Request) (target : request.target = w (address algorithm))
    (gasEq : request.gas = gas algorithm scenario) (calldata : request.calldata = input.words)
    (length : request.calldataSize = w 3) :
    AccountCallSemantics.Precompile request (.value (response algorithm scenario)) := by
  have valid : MemorySemantics.touchSize? Core.Word.zero Core.Word.zero request.calldataSize = some (w 32) := by
    rw [length]; decide +kernel
  cases algorithm <;> cases scenario
  · rw [show response .sha256 .funded = ⟨true, [(Core.Word.zero, digest .sha256)], w 32⟩ from rfl]
    apply AccountCallSemantics.Precompile.sha256 target valid (by rw [gasEq, length]; decide)
    rw [calldata, length]
    exact .last (by decide +kernel) (by decide +kernel)
  · exact AccountCallSemantics.Precompile.sha256Underfunded target valid (by rw [gasEq, length]; decide)
  · rw [show response .ripemd160 .funded = ⟨true, [(Core.Word.zero, digest .ripemd160)], w 32⟩ from rfl]
    apply AccountCallSemantics.Precompile.ripemd160 target valid (by rw [gasEq, length]; decide)
    rw [calldata, length]
    exact .last (by decide +kernel) (by decide +kernel)
  · exact AccountCallSemantics.Precompile.ripemd160Underfunded target valid (by rw [gasEq, length]; decide)

private theorem invoked_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    RuntimeCallEffectsSemantics.Call (fun _ => AccountCallSemantics.noChildren) .ordinary
      (gas algorithm scenario) (w (address algorithm)) (w 0) (w 0) (w 3) (w 32) (w 32)
      (afterThird object).external (.value (.word (status scenario))) (afterCall object algorithm scenario).external := by
  apply RuntimeCallEffectsSemantics.Call.invoked (.inr (.inl rfl)) (by intros _ nonzero; exact False.elim (nonzero rfl))
  apply CallTransportSemantics.Execute.ready (inputSize := w 32) (outputSize := w 64)
  · change MemorySemantics.touchSize? third.size (w 0) (w 3) = some (w 32)
    decide +kernel
  · change MemorySemantics.touchSize? (w 32) (w 32) (w 32) = some (w 64)
    decide +kernel
  have computed := precompile_source algorithm scenario
    (CallTransportSemantics.request
      (RuntimeCallEffectsSemantics.arguments .ordinary (afterThird object).external (gas algorithm scenario)
        (w (address algorithm)) (w 0) (w 0) (w 3) (w 32) (w 32)) input.words)
    (target_masked algorithm) rfl rfl rfl
  cases scenario
  case funded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response algorithm .funded)
      (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · exact AccountCallSemantics.Dispatch.succeeded
        (transferred := RuntimeCallEffectsSemantics.shared (afterThird object).external)
        (.inr (by change ¬w 0 > w 10; decide +kernel)) rfl (.precompile computed) rfl
    · apply MemoryCopySemantics.From.done (size := w 64)
      · change MemorySemantics.touchSize? (w 64) (w 32) (w 32) = some (w 64)
        decide +kernel
      · exact output_copied algorithm
  case underfunded =>
    apply CallTransportSemantics.Dispatch.returned (input := input) (response := response algorithm .underfunded)
      (result := .value .unit)
    · change ¬w 0 > w 1023
      decide +kernel
    · exact input_copied
    · rfl
    · exact AccountCallSemantics.Dispatch.refused
        (transferred := RuntimeCallEffectsSemantics.shared (afterThird object).external)
        (.inr (by change ¬w 0 > w 10; decide +kernel)) rfl (.precompile computed) rfl
    · exact .done rfl (.empty _ _ _ _)

private theorem call_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (invoked algorithm scenario) (afterThird object) (.value (.word (status scenario)))
      (afterCall object algorithm scenario) := by
  cases algorithm <;> cases scenario <;> apply Semantics.EvalExpr.call rfl
  all_goals first
    | exact (.cons (.word (text := "100") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "71") rfl) (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "1000") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact (.cons (.word (text := "719") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "3") rfl) (.cons (.word (text := "32") rfl) (.cons (.word (text := "32") rfl) .nil)))))))
    | exact .external (by rfl) rfl (.call (invoked_source object .sha256 .funded))
    | exact .external (by rfl) rfl (.call (invoked_source object .sha256 .underfunded))
    | exact .external (by rfl) rfl (.call (invoked_source object .ripemd160 .funded))
    | exact .external (by rfl) rfl (.call (invoked_source object .ripemd160 .underfunded))

private theorem store_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      (stored algorithm scenario) (afterThird object) (.value .unit) (afterStore object algorithm scenario) := by
  apply Semantics.EvalExpr.call rfl (.cons (.word (text := "64") rfl) (.cons (call_source object algorithm scenario) .nil))
  cases algorithm <;> cases scenario <;>
    exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none) []
      returned (afterStore object algorithm scenario) result (finalState object algorithm scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "32") rfl) (.cons (.word (text := "33") rfl) .nil)
  · cases algorithm <;> cases scenario <;>
      exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (algorithm : Algorithm) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code algorithm scenario)] (RuntimeCallEffectsSemantics.effects none)
      (AccountRuntime.frameFunction (code algorithm scenario)) [] (initial object) result
      (finalState object algorithm scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (first_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (second_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (third_source object algorithm scenario))
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (store_source object algorithm scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object algorithm scenario))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "call", "return"]

theorem eligible (algorithm : Algorithm) (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported [AccountRuntime.frameFunction (code algorithm scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, seeds, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["0", "97"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "mstore8" ["1", "98"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "mstore8" ["2", "99"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases algorithm <;> cases scenario <;> first
        | exact atoms _ .word "call" ["100", "2", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["71", "2", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["1000", "3", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "call" ["719", "3", "0", "0", "3", "32", "32"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["32", "33"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallCorrespondence.supported false name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩))))))))
  · exact .inr (.inl rfl)
  · exact .inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩)))))

/-- Public consumer for both digests: actual compilation success is the only
premise besides the independent source derivation. -/
theorem public_resumes (algorithm : Algorithm) (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program algorithm scenario) ["Digest"] 64 none [] = .ok object) :
    ∃ value, ContractCallCorrespondence.PublicMessageRel context result (finalState object algorithm scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallCorrespondence.compileObject_resumes_exact (code := code algorithm scenario) (by rfl) accepted
    (eligible algorithm scenario names_supported) context rfl (source object algorithm scenario)

/-- Published test vectors for "abc": FIPS 180-4 for SHA-256 and the
designers' list for RIPEMD-160. -/
def expected : Algorithm → Nat
  | .sha256 => 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  | .ripemd160 => 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

theorem digest_eq (algorithm : Algorithm) : digest algorithm = w (expected algorithm) := by
  cases algorithm <;> decide +kernel

private def digestBytes (algorithm : Algorithm) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (expected algorithm / 256 ^ (31 - index) % 256)

private def check (algorithm : Algorithm) (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program algorithm scenario) ["Digest"] 64 none [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"digest correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"digest correspondence: zero fuel completed: {reprStr outcome}")
  let expectedBytes := if scenario = .underfunded then List.replicate 32 0 ++ [0] else digestBytes algorithm ++ [1]
  for receipt in [Contract.runWithReceipt prepared 100000000, Contract.resumeWithReceipt checkpoint 100000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes && storage.isEmpty && receipt.logs.isEmpty && receipt.balances == [(w 0, w 10)] do
          throw (IO.userError s!"digest correspondence: wrong result for {reprStr algorithm} {reprStr scenario}: {reprStr receipt}")
    | outcome =>
        throw (IO.userError s!"digest correspondence: expected return for {reprStr algorithm} {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for algorithm in [Algorithm.sha256, .ripemd160] do
    for scenario in [Scenario.funded, .underfunded] do
      check algorithm scenario

end Digest

def run : IO Unit := do
  for scenario in [Scenario.identity, .underfunded, .transfer, .staticCall] do
    check scenario
  Modes.run
  Digest.run

end Tests.RustHullPrecompileCorrespondence
end
