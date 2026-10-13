import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals

/-! Positive closure receipts retain every actual captured physical slot together
with the original Source association. Map/world growth leaves that captured
canonical environment unchanged. Only forward erasure to the old association
is provided. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

private def slotsFor {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured actual) : Prop :=
  CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical

/-- This predicate refers to the canonical capture retained by the authentic
ordinary or principal association, including physical method slots. -/
def CapturedSlots
    (original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys registry faults mapping world function native bindings parameter result) : Prop := by
  cases original with
  | ordinary _ captured _ _ _ _ _ _ _ _ _ => exact slotsFor captured
  | principal _ captured _ _ _ _ _ _ _ _ _ => exact slotsFor captured

structure Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
    headers keys registry faults mapping world function native bindings parameter result
  slots : CapturedSlots original

theorem CapturedSlots.extend
    {original : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys registry faults mapping world function native bindings parameter result}
    (slots : CapturedSlots original)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    CapturedSlots (original.extend maps worlds) := by
  cases original <;> exact slots

def Association.extend
    (association : Association headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameter result :=
  ⟨association.original.extend maps worlds, association.slots.extend maps worlds⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameter result)

theorem StaticMember.forget
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember
      headers keys registry faults mapping world function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.original⟩

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := member.forget.represents

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
