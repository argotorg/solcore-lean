import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Actual lexical binder receipts transport nonlocal context fields to each
expression certificate. This is a static map over the genuine compiler tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
open Core Frontend SourceInference GenericLexicalStatements

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {initial context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- The same accepted allocations and emitted code are preserved. -/
theorem Tree.discharge_context
    (tree : Tree layouts owner active frame globals onError values source
      (fun context scope id lowered => Dynamic.RuntimeContextFields initial context → certificates context scope id lowered)
      context scope mode statements expected type code)
    (fields : Dynamic.RuntimeContextFields initial context) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction tree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form => exact .returnUnit rest found form
  | returnValue rest found form expressionFound valueType value =>
      exact .returnValue rest found form expressionFound valueType (value fields)
  | tail found form expressionFound valueType value =>
      exact .tail found form expressionFound valueType (value fields)
  | uninitialized found form mono extended ordinary projected allocation annotation same _remaining ih =>
      exact .uninitialized found form mono extended ordinary projected allocation annotation same
        (ih (fields.trans (.ofBinderExtends extended)))
  | initialized found form mono extended ordinary initializerFound sourceType initialValue allocation annotation same _remaining ih =>
      exact .initialized found form mono extended ordinary initializerFound sourceType (initialValue fields)
        allocation annotation same (ih (fields.trans (.ofBinderExtends extended)))
  | discard found form notTail expressionFound value _remaining ih =>
      exact .discard found form notTail expressionFound (value fields) (ih fields)
  | block found form _inner _remaining innerIH remainingIH =>
      exact .block found form (innerIH fields) (remainingIH fields)
  | ifThen found form conditionFound conditionType conditionTree _then _else _remaining thenIH elseIH remainingIH =>
      exact .ifThen found form conditionFound conditionType (conditionTree fields)
        (thenIH fields) (elseIH fields) (remainingIH fields)
  | terminalBlock unique found form _inner stops issued ih =>
      exact .terminalBlock unique found form (ih fields) stops issued
  | terminalIf unique found form conditionFound conditionType conditionTree _then _else thenStops elseStops issued thenIH elseIH =>
      exact .terminalIf unique found form conditionFound conditionType (conditionTree fields)
        (thenIH fields) (elseIH fields) thenStops elseStops issued

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
