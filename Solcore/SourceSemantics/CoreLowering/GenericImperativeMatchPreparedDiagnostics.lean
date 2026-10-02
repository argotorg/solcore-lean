import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchExtraction
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderDiagnosticExtraction

/-! Diagnostic adapters for the existing extraction records. Only the local
operand obligation changes; materialization uses the original Errors and
SiteLedgers constructors on the same Tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
namespace PreparedDiagnostics
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}

def assign
    {context scope mode id node assignment operator rhs rest expected type body}
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode rest) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.statements mode (id :: rest)) expected type (head.emit body (LocalLoop.controlType type)) := by
  let original := ExtractionFor.assign found form head remaining
  exact ⟨original.tree, (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, headErrors registry faults given.2⟩⟩

def initializerAssign
    {context scope assignment operator rhs rest body condition post statements expected type}
    (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment operator rhs)
    (headDiagnostics : SourceCoreRawMetadata.Registry → FunctionCalls.FaultRep → Prop)
    (headErrors : ∀ registry faults, headDiagnostics registry faults → head.ErrorsFor diagnosticPolicy registry faults)
    (remaining : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers rest condition post statements) expected type body) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved
        context scope (.initializers (.assignValue assignment operator rhs :: rest) condition post statements) expected type (head.emit body (LocalLoop.controlType type)) := by
  let original := ExtractionFor.initializerAssign head remaining
  exact ⟨original.tree, (fun registry faults => remaining.diagnostics registry faults ∧ headDiagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, headErrors registry faults given.2⟩⟩

def initializersDone
    {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (loopBody : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.statements false statements) expected type bodyCode)
    (postTree : GenericForHeader.DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) definitions) :
    ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative solved context scope (.initializers [] condition post statements) expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  let original := ExtractionFor.initializersDone conditionFound conditionType conditionTree loopBody postTree.tree nativeTyped
  exact ⟨original.tree, (fun registry faults => loopBody.diagnostics registry faults ∧ postTree.diagnostics registry faults),
    fun registry faults given => original.materialize registry faults ⟨given.1, postTree.materialize registry faults given.2⟩⟩

end PreparedDiagnostics
end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
