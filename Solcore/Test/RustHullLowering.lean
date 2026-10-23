import Solcore.Frontend.RustHull.Contract

/-! Independent runtime and rejection regressions for imported Hull on Core. -/
set_option autoImplicit false
namespace Tests.RustHullLowering
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def w (value : Nat) : Expr := ⟨.word, .word (toString value), none⟩
private def v (name : String) (ty : Ty := .word) : Expr := ⟨ty, .var name, none⟩
private def call (name : String) (args : List Expr) (ty : Ty := .word) : Expr := ⟨ty, .call name args, none⟩
private def stmt (kind : StmtKind) : Stmt := ⟨kind, none⟩
private def ret (value : Expr) : Stmt := stmt (.returnStmt value)
private def assign (name : String) (value : Expr) : Stmt := stmt (.assign (v name value.ty) value)
private def declareLocal (name : String) (ty : Ty := .word) : Stmt := stmt (.letDecl name ty)
private def fn (name : String) (names : List String) (body : List Stmt) (result : Ty := .word) : Function :=
  {name, args := names.map fun name => {name, ty := .word}, ret := result, body}
private def program (functions : List Function) : Program :=
  {entryPoints := ["main"], functions, objects := []}

private def wordResult (label : String) (source : Program) (expected : Nat)
    (arguments : List Nat := []) : IO Unit := do
  let compiled ← get label (compile source "main")
  let expression := Core.Expr.apply compiled.expression
    (bundle (arguments.map fun value => .word (Core.Word.ofNatModulo value)))
  match Core.runStateful 1000000 (.initial expression) with
  | .done (.inRight _ (.word value)) _ => do
    require (value.val == expected) s!"{label}: expected {expected}, received {value.val}"
  | result => throw (IO.userError s!"{label}: {reprStr result}")

private def rejects (label : String) (source : Program) : IO Unit :=
  match compile source "main" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed Hull was accepted")

private def boolTy : Ty := .sum .unit .unit
private def conditional (condition : Expr) (yes no : List Stmt) : Stmt :=
  stmt (.matchStmt boolTy condition [
    {pat := {kind := .con .inr}, binder := "yes", body := yes},
    {pat := {kind := .con .inl}, binder := "no", body := no}])

private def yn (name : String) : YulName := {name}
private def yw (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def yc (name : String) (args : List YulExpr := []) : YulExpr :=
  ⟨.call (yn name) args, none⟩
private def ye (name : String) (args : List YulExpr := []) : YulStmt :=
  ⟨.expression (yc name args), none⟩
private def objectProgram (body : List YulStmt) : Program :=
  {entryPoints := [], functions := [], objects := [
    .object "runtime" {stmts := [stmt (.assembly body)], functions := []} [] none]}

private def prepare (label : String) (source : Program) (context : Contract.Context := {}) : IO Contract.Prepared :=
  get label (Contract.prepare source ["runtime"] context)

private def contractRejects (label : String) (source : Program) : IO Unit :=
  match Contract.prepare source ["runtime"] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed runtime object was accepted")

private def returned (label : String) (outcome : Contract.Outcome) (expected : List UInt8)
    (storage : Core.WordMapping.Entries := []) : IO Unit :=
  match outcome with
  | .returned bytes actualStorage => do
    require (bytes == expected) s!"{label}: unexpected returned bytes {reprStr bytes}"
    require (actualStorage == storage) s!"{label}: unexpected storage {reprStr actualStorage}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def callsAndRecursion : IO Unit := do
  let weighted := fn "weighted" ["a", "b", "c"] [ret
    (call "add" [call "add" [call "mul" [v "a", w 100], call "mul" [v "b", w 10]], v "c"])]
  wordResult "three argument call" (program [weighted,
    fn "main" [] [ret (call "weighted" [w 1, w 3, w 5])]]) 135
  wordResult "local and function namespaces are separate" (program [weighted,
    fn "main" [] [declareLocal "weighted", assign "weighted" (w 99),
      ret (call "weighted" [w 1, w 3, w 5])]]) 135
  wordResult "parameter and function namespaces are separate" (program [weighted,
    fn "main" ["weighted"] [ret (call "weighted" [w 1, w 3, w 5])]]) 135 [99]
  let recurse : Expr := ⟨.word, .ifThen .word
    (call "eq" [v "n", w 0] boolTy) (w 1)
    (call "mul" [v "n", call "factorial" [call "sub" [v "n", w 1]]]), none⟩
  wordResult "recursive function cells" (program [
    fn "main" ["n"] [ret (call "factorial" [v "n"])],
    fn "factorial" ["n"] [ret recurse]]) 720 [6]
  let even : Expr := ⟨.word, .ifThen .word (call "eq" [v "n", w 0] boolTy)
    (w 1) (call "odd" [call "sub" [v "n", w 1]]), none⟩
  let odd : Expr := ⟨.word, .ifThen .word (call "eq" [v "n", w 0] boolTy)
    (w 0) (call "even" [call "sub" [v "n", w 1]]), none⟩
  wordResult "mutual recursion" (program [fn "odd" ["n"] [ret odd],
    fn "main" [] [ret (call "even" [w 8])], fn "even" ["n"] [ret even]]) 1

private def localsAndLoops : IO Unit := do
  wordResult "block local shadowing" (program [fn "main" [] [
    declareLocal "x", assign "x" (w 1), stmt (.block [declareLocal "x", assign "x" (w 99)]), ret (v "x")]]) 1
  wordResult "loop continue post and break" (program [fn "main" [] [
    declareLocal "total", assign "total" (w 0),
    stmt (.forLoop [declareLocal "i", assign "i" (w 0)] (call "lt" [v "i", w 10] boolTy)
      [assign "i" (call "add" [v "i", w 1])]
      [conditional (call "eq" [v "i", w 2] boolTy) [stmt .continueStmt] [],
       conditional (call "eq" [v "i", w 5] boolTy) [stmt .breakStmt] [],
       assign "total" (call "add" [v "total", v "i"])]), ret (v "total")]]) 8
  rejects "loop initializer scope ends" (program [fn "main" [] [
    stmt (.forLoop [declareLocal "i"] ⟨.bool, .bool false, none⟩ [] []), ret (v "i")]])
  wordResult "return exits enclosing loop" (program [fn "main" [] [
    stmt (.forLoop [] ⟨.bool, .bool true, none⟩ [] [ret (w 43)]), ret (w 99)]]) 43

private def productsAndMatches : IO Unit := do
  let payloadTy : Ty := .product .word .word
  let choiceTy : Ty := .sum .unit .word
  let selectArg : Function := {
    name := "select"
    args := [
      {name := "unused", ty := .unit}, {name := "pair", ty := payloadTy},
      {name := "choice", ty := choiceTy}]
    ret := .word
    body := [stmt (.matchStmt choiceTy (v "choice" choiceTy) [
      {pat := {kind := .con .inl}, binder := "u", body := [ret (w 0)]},
      {pat := {kind := .con .inr}, binder := "selected", body := [ret
        (call "add" [call "add" [
          call "mul" [⟨.word, .fst (v "pair" payloadTy), none⟩, w 100],
          call "mul" [⟨.word, .snd (v "pair" payloadTy), none⟩, w 10]], v "selected"])]}])]}
  wordResult "unit product and sum arguments" (program [selectArg, fn "main" [] [ret
    (call "select" [⟨.unit, .unit, none⟩, ⟨payloadTy, .pair (w 1) (w 3), none⟩,
      ⟨choiceTy, .inr choiceTy (w 5), none⟩])]]) 135
  let pairTy : Ty := .product .word (.product .word .word)
  let pair : Expr := ⟨pairTy, .pair (w 1) ⟨.product .word .word, .pair (w 2) (w 3), none⟩, none⟩
  let tail : Expr := ⟨.product .word .word, .snd (v "p" pairTy), none⟩
  let middle : Expr := ⟨.word, .fst tail, none⟩
  let first : Expr := ⟨.word, .fst (v "p" pairTy), none⟩
  let last : Expr := ⟨.word, .snd tail, none⟩
  wordResult "nested product assignment" (program [fn "main" [] [
    declareLocal "p" pairTy, assign "p" pair, stmt (.assign middle (w 7)),
    ret (call "add" [call "add" [call "mul" [first, w 100], call "mul" [middle, w 10]], last])]]) 173
  let sumTy : Ty := .sum .word (.sum .word .word)
  let sum : Expr := ⟨sumTy, .inK 2 sumTy (w 9), none⟩
  let arm (index bonus : Nat) : Alt := {
    pat := {kind := .con (.inK index)}, binder := "payload",
    body := [ret (call "add" [v "payload", w bonus])]}
  wordResult "third sum constructor" (program [fn "main" [] [
    stmt (.matchStmt sumTy sum [arm 0 100, arm 1 200, arm 2 300])]]) 309
  wordResult "word match and wildcard" (program [fn "main" [] [
    stmt (.matchStmt .word (w 17) [
      {pat := {kind := .intLit "0x10"}, binder := "x", body := [ret (w 1)]},
      {pat := {kind := .wildcard}, binder := "x", body := [ret (v "x")]}])]]) 17

private def malformed : IO Unit := do
  rejects "wrong word annotation" (program [fn "main" [] [ret ⟨.bool, .word "7", none⟩]])
  rejects "wrong injection annotation" (program [fn "main" [] [ret
    ⟨.word, .inl (.sum .word .unit) (w 1), none⟩]])
  rejects "wrong pair annotation" (program [fn "main" [] [ret
    ⟨.word, .pair (w 1) (w 2), none⟩]])
  rejects "projection annotation mismatch" (program [fn "main" [] [ret
    ⟨.bool, .fst ⟨.product .word .word, .pair (w 1) (w 2), none⟩, none⟩]])
  rejects "branch result mismatch" (program [fn "main" [] [ret
    ⟨.word, .ifThen .word ⟨.bool, .bool true, none⟩ (w 1) ⟨.unit, .unit, none⟩, none⟩]])
  rejects "sum constructor out of range" (program [fn "main" [] [ret
    ⟨.sum .word .word, .inK 2 (.sum .word .word) (w 1), none⟩]])
  rejects "sum payload mismatch" (program [fn "main" [] [ret
    ⟨.sum .unit .word, .inl (.sum .unit .word) (w 1), none⟩]])
  rejects "wrong match target" (program [fn "main" [] [
    stmt (.matchStmt .unit (w 1) []), ret (w 0)]])
  rejects "sum pattern on a word" (program [fn "main" [] [
    stmt (.matchStmt .word (w 1) [
      {pat := {kind := .con .inl}, binder := "x", body := [ret (w 0)]}])]])
  rejects "literal assignment target" (program [fn "main" [] [stmt (.assign (w 1) (w 2)), ret (w 0)]])
  rejects "function return mismatch" (program [fn "main" [] [ret ⟨.unit, .unit, none⟩]])
  rejects "callee result annotation mismatch" (program [fn "helper" [] [ret (w 1)],
    fn "main" [] [ret (call "helper" [] .bool)]])
  rejects "recursive type reference is explicit" (program [fn "main" [] [
    declareLocal "list" (.namedRef "List"), ret (w 0)]])
  rejects "residual function layout is explicit" (program [fn "main" [] [
    declareLocal "closure" (.function [.word] .word), ret (w 0)]])
  rejects "unbound local" (program [fn "main" [] [ret (v "missing")]])
  rejects "wrong call arity" (program [fn "helper" ["x"] [ret (v "x")],
    fn "main" [] [ret (call "helper" [])]])
  rejects "unknown callee" (program [fn "main" [] [ret (call "missing" [])]])
  rejects "duplicate functions" (program [fn "main" [] [ret (w 1)], fn "main" [] [ret (w 2)]])
  rejects "duplicate arguments" (program [fn "main" ["x", "x"] [ret (v "x")]])
  rejects "unexported entry" {entryPoints := [], functions := [fn "main" [] [ret (w 1)]], objects := []}
  for control in [StmtKind.breakStmt, .continueStmt] do
    rejects "loop transfer outside loop" (program [fn "main" [] [stmt control, ret (w 0)]])
    rejects "invalid control after return" (program [fn "main" [] [ret (w 0), stmt control]])
  rejects "product assignment type mismatch" (program [fn "main" [] [
    declareLocal "x", stmt (.assign (v "x") ⟨.bool, .bool true, none⟩), ret (v "x")]])
  let hidden := Effects.slotName "exit"
  rejects "reserved local" (program [fn "main" [] [declareLocal hidden, ret (w 0)]])
  rejects "reserved parameter" (program [fn "main" [hidden] [ret (w 0)]])
  rejects "reserved read" (program [fn "main" [] [ret (v hidden)]])
  rejects "reserved match binder" (program [fn "main" [] [
    stmt (.matchStmt .word (w 1) [
      {pat := {kind := .wildcard}, binder := hidden, body := [ret (w 0)]}])]])
  rejects "reserved global" (program [fn hidden [] [ret (w 0)], fn "main" [] [ret (w 0)]])
  contractRejects "reserved Yul local" (objectProgram [⟨.letDecl [yn hidden] (some (yw 1)), none⟩])
  contractRejects "reserved Yul assignment" (objectProgram [⟨.assign [yn hidden] (yw 1), none⟩])
  contractRejects "reserved Yul read" (objectProgram [ye "pop" [⟨.ident (yn hidden), none⟩]])
  contractRejects "duplicate object names" {entryPoints := [], functions := [], objects := [
    .object "runtime" {stmts := [], functions := []} [] none,
    .object "runtime" {stmts := [], functions := []} [] none]}

private def yulHullBridge : IO Unit := do
  let weighted := fn "weighted" ["a", "b", "c"] [ret
    (call "add" [call "add" [call "mul" [v "a", w 100], call "mul" [v "b", w 10]], v "c"])]
  let main (expression : YulExpr) := fn "main" [] [declareLocal "result",
    stmt (.assembly [⟨.assign [yn "result"] expression, none⟩]), ret (v "result")]
  wordResult "explicit Yul to Hull call" (program [weighted,
    main (yc "usr$weighted" [yw 1, yw 3, yw 5])]) 135
  wordResult "Yul local function retains explicit Hull scope" (program [weighted,
    fn "main" [] [declareLocal "result", stmt (.assembly [
      ⟨.functionDef (yn "wrapper") [yn "x"] [yn "y"] [
        ⟨.assign [yn "y"] (yc "usr$weighted" [yw 1, yw 3, ⟨.ident (yn "x"), none⟩]), none⟩], none⟩,
      ⟨.letDecl [yn "weighted"] (some (yw 99)), none⟩,
      ⟨.assign [yn "result"] (yc "wrapper" [yw 5]), none⟩]), ret (v "result")]]) 135
  let record := fn "record" ["value"] [
    stmt (.expression (call "sstore" [w 1, v "value"] .unit)), ret (v "value")]
  let store := fn "store" ["value"] [
    stmt (.expression (call "sstore" [w 2, v "value"] .unit))] .unit
  let combine := fn "combine" ["a", "b"] [ret (call "add" [call "mul" [v "a", w 10], v "b"])]
  let effectSource : Program := {entryPoints := [], functions := [record, store, combine], objects := [
    .object "runtime" {functions := [], stmts := [stmt (.assembly [
      ye "usr$store" [yw 17],
      ye "mstore" [yw 0, yc "usr$combine" [yc "usr$record" [yw 1], yc "usr$record" [yw 2]]],
      ye "return" [yw 0, yw 32]])]} [] none]}
  let effects ← prepare "Yul to Hull side effects" effectSource
  returned "Yul to Hull arguments execute right to left" (Contract.run effects)
    (List.replicate 31 0 ++ [12])
    [(Core.Word.ofNatModulo 2, Core.Word.ofNatModulo 17),
     (Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 1)]
  rejects "unknown explicit Hull function" (program [main (yc "usr$missing")])
  rejects "explicit Hull call arity" (program [weighted, main (yc "usr$weighted" [yw 1])])
  rejects "plain Hull call is not silently renamed" (program [weighted,
    main (yc "weighted" [yw 1, yw 3, yw 5])])
  for ty in [Ty.unit, .bool, .product .word .word, .sum .unit .word] do
    let target : Function := {
      name := "incompatible"
      args := [{name := "x", ty}]
      ret := .word
      body := [ret (w 0)]}
    rejects "Yul Hull argument requires layout conversion" (program [target,
      main (yc "usr$incompatible" [yw 0])])
  let boolReturn := fn "boolean" [] [ret ⟨.bool, .bool true, none⟩] .bool
  rejects "Yul Hull Bool result requires layout conversion" (program [boolReturn,
    main (yc "usr$boolean")])
  let pairTy : Ty := .product .word .word
  let pairReturn := fn "pair" [] [ret ⟨pairTy, .pair (w 1) (w 2), none⟩] pairTy
  rejects "Yul Hull aggregate result requires layout conversion" (program [pairReturn,
    main (yc "usr$pair")])
  rejects "Yul Hull Unit result used as a word" (program [fn "unit" [] [] .unit,
    main (yc "usr$unit")])

private def objectSelection : IO Unit := do
  let leaf := Object.object "runtime" {functions := [], stmts := [
    stmt (.assembly [ye "mstore" [yw 0, yw 42], ye "return" [yw 0, yw 32]])]} [] none
  let nested : Program := {entryPoints := [], functions := [], objects := [
    .object "deployment" {stmts := [], functions := []} [leaf] none]}
  let prepared ← get "nested runtime object" (Contract.prepare nested ["deployment", "runtime"])
  returned "selected nested object" (Contract.run prepared) (List.replicate 31 0 ++ [42])
  for path in [[], ["runtime"], ["deployment", "missing"]] do
    match Contract.prepare nested path with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"unknown object path accepted: {reprStr path}")
  let hiddenLeaf := Object.object "runtime" {functions := [], stmts := [
    stmt (.expression (call "outerOnly" []))]} [] none
  let isolated : Program := {entryPoints := [], functions := [], objects := [
    .object "deployment" {stmts := [], functions := [fn "outerOnly" [] [ret (w 42)]]}
      [hiddenLeaf] none]}
  match Contract.prepare isolated ["deployment", "runtime"] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "inner object captured an outer object function")

private def effectsAndResume : IO Unit := do
  let store := [(Core.Word.ofNatModulo 5, Core.Word.ofNatModulo 11)]
  let bytes := List.replicate 31 (0 : UInt8) ++ [11]
  let prepared ← prepare "return effects" (objectProgram [
    ye "sstore" [yw 5, yw 11], ye "mstore" [yw 0, yc "sload" [yw 5]],
    ye "return" [yw 0, yw 32], ye "sstore" [yw 5, yw 99]])
    {storage := [(Core.Word.ofNatModulo 5, Core.Word.ofNatModulo 3)]}
  returned "return halts later effects" (Contract.run prepared) bytes store
  match Contract.run prepared 1 with
  | .outOfFuel pending => returned "contract fuel resumes" (Contract.resume pending) bytes store
  | result => throw (IO.userError s!"expected suspended Core execution: {reprStr result}")
  let stopped ← prepare "stop" (objectProgram [ye "stop", ye "sstore" [yw 5, yw 99]])
  returned "stop halts effects" (Contract.run stopped) []
  let reverted ← prepare "revert" (objectProgram [ye "sstore" [yw 5, yw 99],
    ye "mstore8" [yw 0, yw 42], ye "revert" [yw 0, yw 1]])
  match Contract.run reverted with
  | .reverted [42] => pure ()
  | other => throw (IO.userError s!"revert did not preserve exact bytes: {reprStr other}")
  let context ← prepare "context" (objectProgram [ye "mstore" [yw 0, yc "callvalue"],
    ye "return" [yw 0, yw 32]]) {value := Core.Word.ofNatModulo 9}
  returned "call value context" (Contract.run context) (List.replicate 31 0 ++ [9])
  let bounded ← prepare "return byte limit" (objectProgram [ye "return" [yw 0, yw 2]])
  match Contract.run bounded 1000000 1 with
  | .exportError _ => pure ()
  | other => throw (IO.userError s!"return byte export limit was ignored: {reprStr other}")
  let invalid ← prepare "invalid" (objectProgram [ye "invalid", ye "sstore" [yw 5, yw 99]])
  match Contract.run invalid with
  | .invalid => pure ()
  | other => throw (IO.userError s!"invalid instruction did not halt: {reprStr other}")
  let copy ← prepare "copy effects" (objectProgram [
    ye "calldatacopy" [yw 0, yw 0, yw 4], ye "mcopy" [yw 1, yw 0, yw 3],
    ye "return" [yw 0, yw 4]]) {calldata := [1, 2, 3, 4]}
  returned "overlapping memory copy uses source snapshot" (Contract.run copy) [1, 1, 2, 3]
  let transient ← prepare "transient storage" (objectProgram [
    ye "tstore" [yw 5, yw 17], ye "mstore" [yw 0, yc "tload" [yw 5]],
    ye "return" [yw 0, yw 32]])
  returned "transient effects do not modify persistent storage" (Contract.run transient)
    (List.replicate 31 0 ++ [17])
  let callee := fn "record" ["value"] [
    stmt (.expression (call "sstore" [w 1, v "value"] .unit)), ret (v "value")]
  let combine := fn "combine" ["a", "b"] [ret (call "add" [call "mul" [v "a", w 10], v "b"])]
  let ordered : Program := {entryPoints := [], functions := [callee, combine], objects := [
    .object "runtime" {functions := [], stmts := [
      stmt (.expression (call "mstore" [w 0,
        call "combine" [call "record" [w 1], call "record" [w 2]]] .unit)),
      stmt (.expression (call "return" [w 0, w 32] .unit))]} [] none]}
  let ordered ← prepare "Hull argument evaluation order" ordered
  returned "Hull arguments execute left to right" (Contract.run ordered)
    (List.replicate 31 0 ++ [12]) [(Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 2)]
  let calldata ← prepare "calldata" (objectProgram [ye "mstore" [yw 0, yc "calldataload" [yw 0]],
    ye "return" [yw 0, yw 32]]) {calldata := [1, 2]}
  returned "calldata zero padding" (Contract.run calldata) ([1, 2] ++ List.replicate 30 0)

def run : IO Unit := do
  callsAndRecursion
  localsAndLoops
  productsAndMatches
  malformed
  yulHullBridge
  objectSelection
  effectsAndResume

end Tests.RustHullLowering
