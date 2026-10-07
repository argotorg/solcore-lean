import Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMatchPrefixAdmission

/-! Genuine Source allocations instantiate match readiness at the actual
selection post. Each restore consumes the same reached body state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- The actual hidden and binder Source allocations establish deep heap
typing; the actual administrative receipt authenticates reached row history. -/
theorem prefix_transfers (source : TypedSource) :
    ProtectedStateMatchReady.PrefixTransfers callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) source where
  hidden := by
    intro initial reached first last context type value location admitted valueTyped allocated frame
    exact CallableIndexedOwnedMatchAdmission.after_hidden bridge first last admitted valueTyped allocated frame
  arm := by
    intro initial reached first last context armContext control resolution type caseFacts value hidden
      location statements bindings environment armEnvironment admitted valueTyped hiddenAllocated
      casesTyped selected extended allocated frame
    exact (CallableIndexedOwnedMatchPrefixAdmission.after_arm_prefix bridge first last
      admitted valueTyped hiddenAllocated casesTyped selected extended allocated frame).1
  restore_arm := by
    intro scope selectedScope canonical selectedCanonical returnTo context armContext binders extended
      mapping world heap store state admitted
    exact CallableIndexedOwnedMatchPrefixAdmission.restore_arm bridge returnTo extended state admitted
  restore_parent := by
    intro scope selectedScope canonical selectedCanonical returnTo context mapping world heap store state admitted
    exact CallableIndexedOwnedMatchPrefixAdmission.restore_parent bridge returnTo state admitted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness
