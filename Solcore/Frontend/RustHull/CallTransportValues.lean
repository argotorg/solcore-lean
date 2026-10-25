import Solcore.Frontend.RustHull.CallTransportSemantics
import Solcore.Frontend.RustHull.Calls
import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence

/-! The caller and account dispatcher agree on the actual callback packets. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CallTransportCorrespondence
open Core Correspondence ScalarExecution CallTransportSemantics

def requestValues (request : Request) : List Core.Value :=
  [.word request.target, .word request.caller, .word request.value, .bool request.isStatic,
    .word request.depth, .word request.gas, WordMapping.encode request.calldata, .word request.calldataSize]
def requestValue (request : Request) : Core.Value := bundleValues (requestValues request)
def responseValues (response : Response) : List Core.Value :=
  [.bool response.success, WordMapping.encode response.data, .word response.size]
def responseValue (response : Response) : Core.Value := bundleValues (responseValues response)

inductive ResponseRel : Semantics.Result Response → Core.Value → Prop where
  | returned (response : Response) : ResponseRel (.value response) (.inRight .word (responseValue response))
  | language (reason : Word) : ResponseRel (.fault (.language reason)) (.inLeft Calls.responseType (.word reason))

end Solcore.Frontend.RustHull.CallTransportCorrespondence
