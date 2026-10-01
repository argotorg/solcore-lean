import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint

/-! One recursive guarded statement tree, with the same child family at every
loop depth. The old lexical fragment supplies return and tail leaves. Ordinary
bindings, assignments, block/if and loop transfers share the actual static
administrative context. Whole contextual extraction, for, match and unary
assignment are separate boundaries. No runtime execution is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context
open GenericLexicalStatements (absentRequest initializedRequest sequence)

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (definitions : DataEnvironment)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    SourceSemantics.Context → Scope → Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | lexical {context scope mode statements expected type code}
      (fragment : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError
        values source expressions administrative definitions registry faults context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode statements expected type code
  | uninitialized {context nextContext scope mode id node binder rest expected type body payload}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : values.checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest source scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (absentRequest source scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        nextContext ((binder.id, payload) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (.letE annotation.expression body)
  | initialized {context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
      (monomorphic : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : source.lookupExpression? initializer = some initializerNode)
      (sourceType : initializerNode.type = binder.scheme.body)
      (initial : expressions context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
        (layouts.allocatorAt owner active onError) (initializedRequest source scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults nextContext ((binder.id, lowered.type) :: scope) mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (sequence type lowered.expression annotation.expression body)

  | discard {context scope mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : expressions context scope expression lowered)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | block {context scope mode id node statements rest expected type innerCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (inner : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false statements expected type innerCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalLoop.sequence type innerCode body)
  | ifThen {context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false thenBody expected type thenCode)
      (elseTree : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope false (elseBody.getD []) expected type elseCode)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) body)

  | assignment {context scope mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context (expressions context) scope administrative definitions assignment operator rhs)
      (errors : head.Errors registry faults)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type))

  | breaking {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (LocalLoop.breaking type)
  | continuing {context scope mode id node rest expected type}
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type (LocalLoop.continuing type)
  | whileLoop {context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body reason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope false statements expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) definitions)
      (remaining : Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode rest expected type body) :
      Tree layouts owner active frame globals onError values source expressions administrative definitions registry faults
        context scope mode (id :: rest) expected type
        (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) body)

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
