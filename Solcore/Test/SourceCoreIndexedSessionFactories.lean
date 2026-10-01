import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceCoreIndexedSession.CallableFactory
#check_failure Solcore.Frontend.SourceCoreIndexedSession.prepareCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.issueCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Recipe.named
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Session.register

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSessionFactories
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "enum Functions { Put(function(Word) returns (Word)) }",
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function named() returns (function(Word) returns (Word)) { return inc; }",
  "function boxed(f: function(Word) returns (Word)) returns (Functions) { return .Put(f); }",
  "function unbox(v: Functions) returns (function(Word) returns (Word)) { match (v) { case .Put(f) { return f; } } }",
  "function maps(v: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return v; }",
  "function tuples(v: (function(Word) returns (Word), Word)) returns ((function(Word) returns (Word), Word)) { return v; }",
  "function builtin(f: function(Word) returns (integer), n: Word) returns (integer) { return f(n); }",
  "function builtinMap(v: mapping(Word => function(Word) returns (integer)), n: Word) returns (integer) { return v[1](n); }",
  "function missing(v: mapping(Word => function(Word) returns (Word)), n: Word) returns (Word) { return v[n](0); }"
]
private def names : List String := ["inc", "use", "named", "boxed", "unbox", "maps", "tuples", "builtin", "builtinMap", "missing"]
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  match ← session.run key args 300000 with
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"factory language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"factory export: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "factory call exhausted")
  | .error error => throw (IO.userError s!"factory call rejected: {reprStr error}")

example {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) : recipe.compiled = compiled :=
  Recipe.prepare_compiled accepted

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "owned callable factories" content names
  let recipe ← get "callable recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let pending ← match boot.resume 0 with
    | .outOfFuel pending => pure pending | _ => throw (IO.userError "fresh bootstrap did not save checkpoint")
  let initial ← match pending.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"fresh bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "fresh bootstrap exhausted")
  require (initial.inertPrefix.heap.isEmpty && initial.installedGlobalsPresent) "fresh bootstrap changed source boundary"
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let inc ← get "named factory" (← initial.named (← key "inc"))
  require (inc.session.heapSize == initial.heapSize && inc.session.functionCount == 1) "named factory allocated/reinstalled native cells"
  let incAgain ← get "stable named factory" (← inc.session.named (← key "inc"))
  require (inc.value == incAgain.value && incAgain.session.functionCount == 1) "factory changed named handle identity"
  let returned ← execute incAgain.session (← key "named") []
  require (returned.value == inc.value) "factory differs from actual source named export"
  let called ← execute returned.session (← key "use") [inc.value, word 40]
  require (called.value == word 41) "named factory value was not callable"
  let box ← execute called.session (← key "boxed") [inc.value]
  let unboxed ← execute box.session (← key "unbox") [box.value]
  require (unboxed.value == inc.value) "deep nominal named input lost owned handle"
  let fn : TypeSystem.Ty := .function .word .word
  let raw : Value := .mapping (.comptime .word) fn [(word 1, inc.value), (word 1, inc.value)]
  let mapping ← execute unboxed.session (← key "maps") [raw]
  require (mapping.value == raw) "deep mapping factory input changed raw header/order"
  let tuple ← execute mapping.session (← key "tuples") [.product inc.value (word 7)]
  require (tuple.value == .product inc.value (word 7)) "deep product factory input changed handle"
  let converted ← get "builtin factory" (← tuple.session.builtin .wordToInteger)
  require (converted.session.heapSize == tuple.session.heapSize) "builtin factory allocated native cells"
  let integer ← execute converted.session (← key "builtin") [converted.value, word 19]
  require (integer.value == .integer 19) "owned builtin template returned wrong integer"
  let intFn : TypeSystem.Ty := .function .word .integer
  let intMapping : Value := .mapping .word intFn [(word 1, converted.value), (word 1, converted.value)]
  let mappedInteger ← execute integer.session (← key "builtinMap") [intMapping, word 23]
  require (mappedInteger.value == .integer 23) "builtin input inside ordered mapping was not callable"
  let mut allBuiltins := mappedInteger.session
  for function in BuiltinFunctionId.all do
    let imported ← get "complete builtin factory inventory" (← allBuiltins.builtin function)
    discard <| get "builtin type certificate" (imported.session.authenticate 1024 function.type imported.value)
    require (imported.session.heapSize == allBuiltins.heapSize) "builtin inventory changed persistent heap"
    allBuiltins := imported.session
  let rawMissingType : TypeSystem.Ty := .comptime fn
  let missingKey ← key "missing"
  let missingStart ← get "missing-default request" (allBuiltins.start missingKey
    [.mapping (.comptime .word) rawMissingType [], word 1])
  let missingPending ← match ← missingStart.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | _ => throw (IO.userError "missing request did not preserve checkpoint")
  match ← missingPending.resume 300000 with
  | .failed reason session =>
      let after ← get "retained raw diagnostic" (session.diagnostic missingKey reason)
      let before ← get "pending raw diagnostic" (missingPending.diagnostic reason)
      require (decide (before = after)) "checkpoint lost newly interned raw mapping header"
      match after with
      | some diagnostic =>
          require (decide (diagnostic.error = .typeMismatch rawMissingType none) && diagnostic.span.isSome)
            "missing default diagnostic changed raw type or source site"
      | none => throw (IO.userError "missing default reason was not decoded")
      require ((← get "unknown reason" (session.diagnostic missingKey (Core.Word.ofNatModulo (Core.wordModulus - 1)))).isNone)
        "unknown language reason was silently accepted"
  | _ => throw (IO.userError "missing default changed result classification")
  let freshBoot ← artifact.bootstrapFresh
  let fresh ← match freshBoot.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "fresh foreign session bootstrap failed")
  match fresh.authenticate 1024 intFn converted.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "factory capability accepted by foreign session")
  let branchA ← get "branch A builtin" (← initial.builtin .wordToInteger)
  let branchB ← get "branch B builtin" (← initial.builtin .wordToInteger)
  match branchB.session.authenticate 1024 intFn branchA.value with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "builtin export generations collided")
  let missing := { (← key "inc") with arguments := [.bool] }
  match ← mappedInteger.session.named missing with
  | .error {code := .missingEntry _, ..} => pure ()
  | _ => throw (IO.userError "factory accepted unowned specialization")
  IO.println "owned indexed named/builtin factories GREEN"

end Tests.SourceCoreIndexedSessionFactories
