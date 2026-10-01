import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Inventory.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Receipt.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Compiled.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreLambdaTemplates.Export.mk
#check_failure fun (receipt : Solcore.Frontend.SourceCoreLambdaTemplates.Receipt) => { receipt with body := Solcore.Core.Expr.unit }

/-! Actual compiler manifests authenticate source lambda templates after
installation and administrative weakening. Native code/type preservation,
shared mutable capture, scope-free/zero-parameter closures, unused principals,
polymorphic bundles, tampered descriptors/code and typed suspension are tested.
Source closure export and dynamic ancestry remain separate ledger boundaries. -/
set_option autoImplicit false
namespace Tests.SourceCoreLambdaTemplates
open Solcore Solcore.Frontend SourceInference
open SourceCoreLambdaTemplates

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function maker(value: Word) returns (F) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function zero() returns (function() returns (Word)) { return lam() -> Word { return 7; }; }",
    "function unused(value: Word) returns (Word) { let ignored = lam(item) { return item; }; return value; }",
    "function poly(flag: Bool) returns (Word, Bool) { let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function loop(value: Word) returns (F) { let f: F; while (true) { f = lam(delta: Word) -> Word { value = value + delta; return value; }; break; } return f; }",
    "function nestedPoly(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; return (outer(1), outer(flag)); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"lambda template fixture missing: {name}")
private def artifact (program : CheckedProgram) (names : List String) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"lambda template plan failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"lambda template artifact failed: {reprStr error}")

example {definitions : Core.DataEnvironment} {context : Core.Context} {parameter result capturesType : Core.Ty}
    {captures body : Core.Expr} (descriptor : Core.Word)
    (captured : Core.HasType context captures capturesType definitions)
    (typed : Core.HasType (parameter :: context) body result definitions) :
    Core.HasType (parameter :: context) (manifestBody descriptor [] captures body) result definitions :=
  manifestBody_hasType descriptor (by simp) captured typed

example {environment : Core.Environment} {initial final : Core.Store} {captures body : Core.Expr}
    {captureValue value : Core.Value} (descriptor : Core.Word)
    (captureEval : Core.Evaluates environment initial (captures.weakenAt 0) captureValue initial)
    (bodyEval : Core.Evaluates environment initial body value final) :
    ∃ value' final', Core.Evaluates environment initial (manifestBody descriptor [] captures body) value' final' ∧
      Core.ValuesRelated value value' ∧ Core.StoresRelated final final' :=
  manifestBody_related descriptor captureEval bodyEval

private structure Ready (checked : Checked) where
  inventory : Inventory checked
  compiled : Compiled inventory (SourceCoreCompatibleFunctions.representation (.initial checked) 256) 256
private def ready {checked : Checked} (base : Base checked) : IO (Ready checked) := do
  let inventory ← match SourceCoreLambdaTemplates.prepare base with
    | .ok inventory => pure inventory | .error error => throw (IO.userError s!"lambda inventory failed: {reprStr error}")
  let compiled ← match SourceCoreLambdaTemplates.compile inventory (SourceCoreCompatibleFunctions.representation (.initial checked) 256) 256 with
    | .ok compiled => pure compiled | .error error => throw (IO.userError s!"lambda compiler/scanner failed: {reprStr error}")
  pure ⟨inventory, compiled⟩

private def native {checked : Checked} (ready : Ready checked) (owner : Key) (arguments : SourceCoreBasic.LoweredExpr) :
    IO (SourceCoreGeneralEntry.NativeEntry checked.catalog.definitions) := do
  let base := ready.inventory.base
  let function ← match base.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some function => pure function | none => throw (IO.userError "lambda compiled root missing")
  let body ← match SourceCoreGeneralFunctions.assembleCall base.globals base.functions ready.compiled.compilation.closures owner arguments with
    | .ok body => pure body | .error error => throw (IO.userError s!"lambda native assembly failed: {reprStr error}")
  match SourceCoreGeneralEntry.NativeEntry.compile checked.catalog.definitions [] function.signature.resultType body with
  | .ok native => pure native | .error error => throw (IO.userError s!"lambda manifest lost Core typing: {reprStr error}")

private def resumed {definitions : Core.DataEnvironment} (native : SourceCoreGeneralEntry.NativeEntry definitions)
    (fuel : Nat) : IO (SourceCoreGeneralEntry.Result definitions native.resultType) := do
  let result ← match native.run [] fuel with
    | .ok result => pure result | .error error => throw (IO.userError s!"lambda manifest native invocation failed: {reprStr error}")
  match result.checkpoint? with
  | some suspended => pure (suspended.resume 150000)
  | none => pure result

/-- A different descriptor remains Core-typed; source ownership must reject it. -/
private def retag (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with
  | .pair tagged _ => .pair tagged (.word descriptor)
  | other => other

private theorem retag_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty} (descriptor : Core.Word)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter result) definitions) :
    Core.RuntimeValueHasType world (retag value descriptor) (Core.CallableContract.functionType parameter result) definitions := by
  cases typed with
  | pair tagged _ => exact .pair tagged .word

/-- Replacing native lambda code with a constant keeps its type and captures. -/
private def replaceBody (value : Core.Value) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result _ environment)) descriptor =>
      .pair (.pair identity (.closure parameter result
        (Core.LanguageResult.success (.word (w 999))) environment)) descriptor
  | other => other

private theorem replaceBody_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter : Core.Ty}
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter .word) definitions) :
    Core.RuntimeValueHasType world (replaceBody value) (Core.CallableContract.functionType parameter .word) definitions := by
  cases typed with
  | pair tagged descriptor =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment _ =>
        exact .pair (.pair identity (.closure environment (.inRight .word .word))) descriptor

/-- Even a behaviorally transparent, typed edit invalidates cached global code. -/
private def replaceGlobal (value : Core.Value) : Core.Value :=
  match value with
  | .inRight .unit (.closure parameter result body environment) =>
      .inRight .unit (.closure parameter result (.letE .unit (body.weakenAt 0)) environment)
  | other => other

private theorem replaceGlobal_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty}
    (typed : Core.RuntimeValueHasType world value
      (Core.OptionalCell.cellType (.function parameter result)) definitions) :
    Core.RuntimeValueHasType world (replaceGlobal value)
      (Core.OptionalCell.cellType (.function parameter result)) definitions := by
  cases typed with
  | inLeft payload => exact .inLeft payload
  | inRight function =>
    cases function with
    | closure environment body =>
      exact .inRight (.closure environment (.letE .unit
        (by simpa only [Core.Context.insertAt] using body.weakenAt (inserted := .unit) 0)))

private def callTwice {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (value : Core.Value)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType .word .word) definitions)
    (captureLocations : List Nat) : IO Unit := do
  let call := fun n => Core.Expr.apply (.second (.first (.var 0))) (.word (w n))
  let expression := Core.LocalSequence.pair .word .word (call 1) (call 2)
  have body : Core.HasType [Core.CallableContract.functionType .word .word] expression
      (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := Core.State.initial expression [value] store
    typed := .eval stored (.cons typed .nil) body .nil
  }
  for fuel in [0, 11, 150000] do
    let first := checkpoint.resume fuel
    let completed := match first.checkpoint? with
      | some next => next.resume 150000 | none => first
    match completed.observation with
    | .succeeded (.pair (.word left) (.word right)) final =>
      assertTrue (left == w 4 && right == w 6) "lambda calls stopped sharing their mutable lexical cell"
      assertTrue (final.length == store.length + 2) "manifest allocated an extra heap cell during invocation"
      assertTrue (captureLocations.any (fun location => final[location]? == some (.inRight .unit (.word (w 6)))))
        "lambda manifest lost the original source capture location"
    | other => throw (IO.userError s!"typed lambda reuse/resume failed: {reprStr other}")

private def checkClosure {checked : Checked} (ready : Ready checked) (owner : Key) (parameter : Core.Ty)
    (arguments : SourceCoreBasic.LoweredExpr) : IO Unit := do
  let native ← native ready owner arguments
  if same : native.resultType = Core.CallableContract.functionType parameter .word then
    for fuel in [0, 7, 37, 150000] do
      let result ← resumed native fuel
      match success : result.observation with
      | .succeeded value store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store checked.catalog.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType parameter .word) checked.catalog.definitions := by
          obtain ⟨world, stored, typed⟩ := result.success_typed success
          have equal := stored.world_eq
          subst world
          exact ⟨stored, by simpa only [same] using typed⟩
        let exported ← match authenticateCompiled ready.compiled typed.1 value parameter .word typed.2 with
          | .ok exported => pure exported | .error error => throw (IO.userError s!"lambda exact typed capture authentication failed: {reprStr error}")
        assertTrue (exported.closure.captures.locations.length == exported.template.scope.length)
          "lambda template dropped a lexical source reference"
        assertTrue (exported.template.lambda.owner == owner) "lambda template claimed another source owner"
        match authenticateCompiled ready.compiled typed.1 (retag value (w 999999)) parameter .word
            (retag_typed _ typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "same-typed foreign descriptor was authenticated")
        match authenticateCompiled ready.compiled typed.1 (replaceBody value) parameter .word
            (replaceBody_typed typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "same-typed modified closure body was authenticated")
        if fuel == 150000 then
          if parameterWord : parameter = .word then
            callTwice typed.1 value (by simpa only [parameterWord] using typed.2) exported.closure.captures.locations
          let global ← match ready.inventory.base.globals.head? with
            | some global => pure global | none => throw (IO.userError "lambda fixture has no globals")
          let location := ready.inventory.base.globals.length - 1
          let type := Core.OptionalCell.cellType global.functionType
          if found : (store.map Core.Value.type)[location]? = some type then
            match lookup : store.read? location with
            | none => throw (IO.userError "typed global slot unexpectedly absent")
            | some oldValue =>
              have oldTyped : Core.RuntimeValueHasType (store.map Core.Value.type) oldValue type checked.catalog.definitions := by
                obtain ⟨other, otherLookup, otherTyped⟩ := typed.1.read found
                rw [lookup] at otherLookup
                cases otherLookup
                exact otherTyped
              let changed := replaceGlobal oldValue
              have changedTyped : Core.RuntimeValueHasType (store.map Core.Value.type) changed type checked.catalog.definitions :=
                replaceGlobal_typed oldTyped
              match written : store.write? location changed with
              | none => throw (IO.userError "typed global slot unexpectedly outside heap")
              | some changedStore =>
                have changedStored := typed.1.write found changedTyped written
                match authenticateCompiled ready.compiled changedStored value parameter .word typed.2 with
                | .error (.globalSlotMismatch _) => pure ()
                | _ => throw (IO.userError "same-typed changed global code was authenticated")
          else throw (IO.userError "actual installed global slot had another type")
      | other => throw (IO.userError s!"lambda manifest run did not finish: {reprStr other}")
  else throw (IO.userError "lambda test source result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"lambda template source rejected: {reprStr error}")
  let artifact ← artifact program ["maker", "zero", "unused", "poly", "loop", "nestedPoly"]
  let ready ← ready artifact.prepared
  assertTrue (ready.inventory.unusedPrincipals.any (fun binding => binding.binder.name == "ignored"))
    "unused generic principal falsely required a native lambda emission"
  let maker ← key program "maker"
  let zero ← key program "zero"
  let loop ← key program "loop"
  let poly ← key program "poly"
  let nestedPoly ← key program "nestedPoly"
  assertTrue (ready.compiled.templates.length == 9) "source templates omitted lambda/bundle candidate or included a helper lambda"
  let monoTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = maker)) with
    | some template => pure template | none => throw (IO.userError "actual source lambda manifest not found")
  assertTrue (monoTemplate.scope.length == 1 && monoTemplate.references.length == 1) "source scalar capture omitted"
  let zeroTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = zero)) with
    | some template => pure template | none => throw (IO.userError "zero-parameter manifest missing")
  assertTrue (zeroTemplate.scope.isEmpty && zeroTemplate.references.isEmpty && zeroTemplate.parameterType == .unit)
    "scope-free or zero-parameter lambda gained captures"
  let bundle := ready.compiled.templates.filter (fun template => decide (template.lambda.owner = poly))
  assertTrue (bundle.length == 2 && bundle.all (fun template => !template.lambda.active.isEmpty))
    "principal polymorphic bundle was confused with a monomorphic emitted closure"
  let loopTemplate ← match ready.compiled.templates.find? (fun template => decide (template.lambda.owner = loop)) with
    | some template => pure template | none => throw (IO.userError "lambda nested in loop lost manifest")
  assertTrue (loopTemplate.references != monoTemplate.references)
    "loop/install administrative weakening did not reach captured variables"
  checkClosure ready maker .word ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  checkClosure ready zero .unit ⟨.unit, Core.LanguageResult.success .unit⟩
  checkClosure ready loop .word ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  let nested := ready.compiled.templates.filter (fun template => decide (template.lambda.owner = nestedPoly))
  assertTrue (nested.length == 4 && nested.all (fun template => !template.lambda.active.isEmpty))
    "nested polymorphic templates lost their full selected context"
  assertTrue ((nested.map (fun template => template.lambda.descriptor)).eraseDups.length == 4)
    "nested selected instances collided in the callable descriptor table"
  let nestedNative ← native ready nestedPoly ⟨.bool, Core.LanguageResult.success (.bool true)⟩
  for fuel in [0, 23, 150000] do
    let nestedResult ← resumed nestedNative fuel
    match nestedResult.observation with
    | .succeeded (.pair (.word left) (.word right)) _ =>
      assertTrue (left == w 1 && right == w 1) "nested manifested bundle changed source-call results"
    | other => throw (IO.userError s!"nested manifested bundle failed: {reprStr other}")
  let .pair tagged _ := monoTemplate.carrier | throw (IO.userError "lambda carrier shape changed")
  match decode ready.inventory (.pair tagged (.word (w 999999))) with
  | .error (.descriptorMismatch _ _) => pure () | _ => throw (IO.userError "lambda descriptor tamper accepted")
  let .pair (.pair identity (.lambda parameter result body)) descriptor := monoTemplate.carrier
    | throw (IO.userError "lambda template shape changed")
  let .letE metadata _ := body | throw (IO.userError "lambda manifest body missing")
  match decode ready.inventory (.pair (.pair identity (.lambda parameter result (.letE metadata .unit))) descriptor) with
  | .ok structural =>
    assertTrue (structural.body != monoTemplate.body) "structural decode accidentally authenticated compiler emission history"
  | .error _ => throw (IO.userError "syntactic scanner should distinguish shape from actual cached emission ownership")
  IO.println "lambda manifests/installed templates, typed tamper/capture auth, shared heap, nested bundles and resume GREEN"
end Tests.SourceCoreLambdaTemplates
