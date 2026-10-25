import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.ChildResultSemantics

/-! Independent execution of linked Hull child frames. The catalog identifies
source code by execution address; a separate representation proof must link
that entry to the executable identity stored by the actual runtime.

Children receive the transferred shared state and a fresh local frame. They do
not finalize a transaction: account dispatch commits or restores their shared
state after inspecting the response. The finite-height family counts executed
child frames, independently of the Core evaluator's fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameSemantics
open Core

structure Code where
  program : Program
  body : CodeBlock
  bytes : List UInt8

/-- The source wrapper agrees with the object compiler's entry function. -/
def Code.entry (code : Code) : Function :=
  {name := "$lean$object$entry", args := [], ret := .unit, body := code.body.stmts}

def Code.functions (code : Code) : List Function :=
  code.program.functions ++ code.body.functions ++ [code.entry]

abbrev Catalog := List (Word × Code)

def select (catalog : Catalog) (address : Word) : Option Code :=
  (catalog.find? (fun entry => entry.1 == address)).map Prod.snd

/-- Only block and transaction observations are inherited from the parent.
Message observations, gas, code, memory and return data belong to this child. -/
def initial (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) : RuntimeCallEffectsSemantics.State :=
  let observations := parent.runtime.runtime.runtime.runtime.environment
  let observations : EnvironmentSemantics.State := {observations with
    direct := fun operation => match operation with
      | .address => request.target
      | .caller => request.caller
      | .callvalue => request.value
      | .calldataSize => request.calldataSize
      | .returnDataSize => Word.zero
    gas := some request.gas
    codeSize := Word.ofNatModulo bytes.length
    codeKnown := true
    calldata := request.calldata}
  let runtime : RuntimeEffectsSemantics.State := {
    memory := {}
    storage := {world := shared.world, address := request.target, complete := shared.complete, isStatic := request.isStatic}}
  let environment : RuntimeEnvironmentEffectsSemantics.State := ⟨runtime, observations⟩
  let logs : RuntimeLogEffectsSemantics.State := ⟨environment, shared.logs, shared.logSize⟩
  let account : RuntimeAccountEffectsSemantics.State := ⟨logs, shared.balances⟩
  ⟨⟨account, []⟩, request.depth⟩

/-- The frame wrapper performs a final account lookup before its result is
passed to childResult. An unsuccessful lookup replaces the body status. -/
def completedStatus (status : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    Semantics.Result Semantics.Value :=
  match StorageSemantics.get state.storage.world state.storage.address state.storage.complete with
  | .ok _ => status
  | .error reason => .fault (.language reason)

/-- A finite child execution supplies only source derivations. Code selection
and known bytes are checked before entering its fresh frame. -/
inductive Children (catalog : Catalog)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State)
    (parent : RuntimeCallEffectsSemantics.State) : AccountCallSemantics.Children where
  | executed {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeCallEffectsSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (effects (some code.bytes)) code.entry []
        ⟨[], initial parent request shared code.bytes⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime.runtime response) :
      Children catalog effects parent .ordinary source request shared response
        (RuntimeCallEffectsSemantics.shared final.external)

/-- The first compiled-child instance executes the established effect language
without further message calls. Its result still uses the same account checkpoint. -/
inductive CallFree (catalog : Catalog) (parent : RuntimeCallEffectsSemantics.State) :
    AccountCallSemantics.Children where
  | executed {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeReturnDataEffectsSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (RuntimeReturnDataEffectsSemantics.effects (some code.bytes))
        code.entry [] ⟨[], (initial parent request shared code.bytes).runtime⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime response) :
      CallFree catalog parent .ordinary source request shared response
        (RuntimeCallEffectsSemantics.shared ⟨final.external, request.depth⟩)

def callFreeEffects (catalog : Catalog) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State :=
  RuntimeCallEffectsSemantics.effectsWith (CallFree catalog) image

/-- Height zero still permits local call outcomes such as absent accounts and
insufficient funds. Exhausting this height never invents a source failure. -/
def effectsAt (catalog : Catalog) : Nat → Option (List UInt8) →
    Semantics.ExternalSemantics RuntimeCallEffectsSemantics.State
  | 0, image => RuntimeCallEffectsSemantics.effects image
  | height + 1, image => RuntimeCallEffectsSemantics.effectsWith (Children catalog (effectsAt catalog height)) image

theorem initial_shared (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallEffectsSemantics.shared (initial parent request shared bytes) = shared := by
  cases shared
  rfl

theorem initial_transport (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallEffectsSemantics.transport (initial parent request shared bytes) = ⟨{}, [], Word.zero⟩ := rfl

theorem initial_depth (parent : RuntimeCallEffectsSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    (initial parent request shared bytes).callDepth = request.depth := rfl

theorem completedStatus_found {status : Semantics.Result Semantics.Value} {state : RuntimeEffectsSemantics.State}
    {account : AccountState.Account}
    (found : StorageSemantics.get state.storage.world state.storage.address state.storage.complete = .ok account) :
    completedStatus status state = status := by simp only [completedStatus, found]

end Solcore.Frontend.RustHull.ChildFrameSemantics
