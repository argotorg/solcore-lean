import Solcore.Frontend.RustHull.RuntimeCallModeSemantics
import Solcore.Frontend.RustHull.ChildFrameSemantics

/-! Linked child code is selected by the requested code address. CALLCODE and
DELEGATECALL execute that code at the invoking frame's address, using its
storage. Source derivations count child frames independently of execution fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildFrameModeSemantics
open Core

abbrev Code := ChildFrameSemantics.Code
abbrev Catalog := ChildFrameSemantics.Catalog
abbrev select := ChildFrameSemantics.select
abbrev completedStatus := ChildFrameSemantics.completedStatus

def executionRequest (mode : AccountCallSemantics.Mode) (source : Word)
    (request : AccountCallSemantics.Request) : AccountCallSemantics.Request :=
  {request with target := if mode = .ordinary then request.target else source}

def initial (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) : RuntimeCallModeSemantics.State :=
  ChildFrameSemantics.initial parent (executionRequest mode source request) shared bytes

inductive Children (catalog : Catalog)
    (effects : Option (List UInt8) → Semantics.ExternalSemantics RuntimeCallModeSemantics.State)
    (parent : RuntimeCallModeSemantics.State) : AccountCallSemantics.Children where
  | executed {mode : AccountCallSemantics.Mode} {source : Word} {request : AccountCallSemantics.Request}
      {shared : AccountCallSemantics.Shared} {account : AccountState.Account} {code : Code}
      {status : Semantics.Result Semantics.Value} {final : Semantics.State RuntimeCallModeSemantics.State}
      {response : Semantics.Result AccountCallSemantics.Response}
      (ordinaryAccount : AccountCallSemantics.isPrecompile request.target = false)
      (found : StorageSemantics.lookup request.target shared.world = some account)
      (selected : select catalog request.target = some code)
      (known : account.code = some code.bytes)
      (evaluated : Semantics.EvalFunction code.functions (effects (some code.bytes)) code.entry []
        ⟨[], initial mode source parent request shared code.bytes⟩ status final)
      (responded : ChildResultSemantics.Respond
        (completedStatus status final.external.runtime.runtime.runtime.runtime.runtime)
        final.external.runtime.runtime.runtime.runtime.runtime response) :
      Children catalog effects parent mode source request shared response
        (RuntimeCallModeSemantics.shared final.external)

/-- Child frames at most `height` deep. `initCatalog` holds the init templates
and runtime images of creation; no rule of this file reads it yet. -/
def effectsAt (catalog : Catalog) (initCatalog : ChildFrameSemantics.InitCatalog) : Nat → Option (List UInt8) →
    Semantics.ExternalSemantics RuntimeCallModeSemantics.State
  | 0, image => RuntimeCallModeSemantics.effects image
  | height + 1, image =>
      RuntimeCallModeSemantics.effectsWith (Children catalog (effectsAt catalog initCatalog height)) image

theorem initial_shared (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallModeSemantics.shared (initial mode source parent request shared bytes) = shared :=
  ChildFrameSemantics.initial_shared _ _ _ _

theorem initial_transport (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    RuntimeCallModeSemantics.transport (initial mode source parent request shared bytes) = ⟨{}, [], Word.zero⟩ := rfl

theorem initial_depth (mode : AccountCallSemantics.Mode) (source : Word)
    (parent : RuntimeCallModeSemantics.State) (request : AccountCallSemantics.Request)
    (shared : AccountCallSemantics.Shared) (bytes : List UInt8) :
    (initial mode source parent request shared bytes).callDepth = request.depth := rfl

end Solcore.Frontend.RustHull.ChildFrameModeSemantics
