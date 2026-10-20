import Solcore.Test.SourceCoreGeneralizedBodyExpressionSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! Source evaluation is built from the original lambda, its actual captured
cell and the instantiated static frame. No Core run supplies a body trace. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedBodyExpression
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreNamedBranch (Read)
open Tests.SourceCoreSelectedInterleavedLocal (WordNode)
open Tests.SourceCoreMixedImperative (StoredValue)

 theorem PairAt.children {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context pair.node.id type) :
    ∃ leftType rightType, ExpressionHasType source context left leftType ∧ ExpressionHasType source context right rightType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans pair.found)
    rw [pair.form] at raw
    cases raw with
    | tuple children => cases children with | cons first tail => cases tail with | cons second _ => exact ⟨_,_,first,second⟩

theorem PairAt.evaluates {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {first second : Dynamic.Value}
    (a : Dynamic.ExpressionEvaluates program context evidence source environment before left first middle)
    (b : Dynamic.ExpressionEvaluates program context evidence source environment middle right second after) :
    Dynamic.ExpressionEvaluates program context evidence source environment before pair.node.id (.product first second) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound pair.found)
  · rw [pair.form,pair.requirements,pair.coercions]
    exact .tuple rfl (.cons a (.cons b .nil)) (.cons (.singleton _))
  · rw [pair.coercions]; exact .nil

def PairAt.substitute {source : TypedSource} {left right : ExpressionId}
    (pair : PairAt source left right) (substitution : TypeSystem.Substitution) :
    PairAt (source.applySubstitution substitution) left right := {
  node := pair.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ pair.found
  form := by simp [ExpressionNode.applySubstitution,pair.form,ExpressionForm.applySubstitution]
  requirements := by simp [ExpressionNode.applySubstitution,pair.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,pair.coercions] }

def substituteRead {source : TypedSource} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Read source binder type) (substitution : TypeSystem.Substitution) :
    Read (source.applySubstitution substitution) (binder.applySubstitution substitution) (substitution.apply type) := {
  node := read.node.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ read.found
  form := by simp [ExpressionNode.applySubstitution,read.form,ExpressionForm.applySubstitution,TypedBinder.applySubstitution,ReferenceResolution.applySubstitution]
  raw := by simp [ExpressionNode.rawType,ExpressionNode.applySubstitution,read.coercions,read.type]
  type := by simp [ExpressionNode.applySubstitution,read.type]
  requirements := by simp [ExpressionNode.applySubstitution,read.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,read.coercions] }

def substituteWord {source : TypedSource} (word : WordNode source) (substitution : TypeSystem.Substitution) :
    WordNode (source.applySubstitution substitution) := {
  node := word.node.applySubstitution substitution
  literal := word.literal
  resolution := word.resolution.applySubstitution substitution
  found := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution _ _ _ _ word.found
  form := by simp [ExpressionNode.applySubstitution,word.form,ExpressionForm.applySubstitution]
  target := by simp [word.target]
  requirements := by simp [ExpressionNode.applySubstitution,word.requirements]
  coercions := by simp [ExpressionNode.applySubstitution,word.coercions] }

def LambdaShape.descriptor {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) : Dynamic.GeneralizedClosure :=
  Dynamic.GeneralizedClosure.ofDirectLambda context source environment shape.binder shape.lambda.id
    [shape.parameter] (resultType (.variable shape.typeVariable)) [shape.returned.id]

theorem LambdaShape.captures {source : TypedSource} (shape : LambdaShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) :
    Dynamic.GeneralizedClosureCaptures context source environment shape.binder shape.lambda.id
      (shape.descriptor context environment) :=
  .directLambda (lookupExpression?_sound shape.lambdaFound) shape.lambdaForm
    shape.lambdaRaw shape.lambdaType shape.lambdaRequirements shape.lambdaCoercions

theorem LambdaShape.body_applies {source : TypedSource} (shape : LambdaShape source)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence callerEvidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (argument : Dynamic.Value) (flag : Bool)
    (capturedValue : StoredValue shape.flag captured before (.bool flag))
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution evidence)) :
    Dynamic.CallableApplies program context callerEvidence evidence before
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution evidence))
      [argument] (resultValue argument flag)
      ⟨before.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  let function := (shape.descriptor definitionContext captured).instantiate substitution evidence
  let parameter := shape.parameter.applySubstitution substitution
  let after : Dynamic.Heap := ⟨before.cells ++ [{type := parameter.scheme.body, value := some argument}]⟩
  have allocation : Dynamic.Heap.Allocates before parameter.scheme.body (some argument) ⟨before.cells.length⟩ after := .append
  have parameters : ∃ types callContext,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext := by
    rcases frame.code.occurrence with ⟨id,node,_contains,form,_raw,typed⟩
    rw [form] at typed
    generalize rawEq : TypeSystem.Ty.function
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = raw at typed
    cases typed with
    | lambda names parameters body completes => exact ⟨_,_,parameters⟩
  obtain ⟨types,callContext,parameters⟩ := parameters
  have parameterList : function.parameters = [parameter] := rfl
  rw [parameterList] at parameters
  cases parameters with
  | cons scheme extended tail =>
    cases tail
    cases extended with
    | intro wellformed fresh =>
      have extending : ∃ types, MonoBindersExtend function.source.owner function.context function.parameters
          types (function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) :=
        ⟨_, parameterList.symm ▸ MonoBindersExtend.cons scheme (.intro wellformed fresh) (.nil _)⟩
      obtain ⟨types,extended⟩ := extending
      obtain ⟨final,facts,bodyTyped,_⟩ := CoreLowering.CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
      obtain ⟨middle,_,_,headTyped,_⟩ := Tests.SourceCoreMixedImperative.head_tail bodyTyped
      have returnedFound := lookupStatement?_complete frame.code.graph.nodeOccurrencesUnique
        (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound))
      have returnedForm : (shape.returned.applySubstitution substitution).form = .returnStmt (some shape.result.node.id) := by
        simp [StatementNode.applySubstitution,shape.returnForm,StatementForm.applySubstitution]
      have original := Tests.SourceCoreMixedImperative.form_at frame.code.graph.nodeOccurrencesUnique returnedFound headTyped
      rw [returnedForm] at original
      cases original with
      | returnValue typed =>
        obtain ⟨_,_,_,extraTyped⟩ := (shape.result.substitute substitution).children frame.code.graph.nodeOccurrencesUnique typed
        obtain ⟨_,_,_,zeroTyped⟩ := (shape.extra.substitute substitution).children frame.code.graph.nodeOccurrencesUnique extraTyped
        have firstStored : StoredValue (shape.parameter.applySubstitution substitution)
            ((parameter.id,⟨before.cells.length⟩)::captured) after argument := ⟨_,_,.head,allocation.reads_new,rfl,rfl⟩
        have firstTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.first substitution) firstStored
        have secondTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.second substitution) firstStored
        have captureStored : StoredValue (shape.flag.applySubstitution substitution)
            ((parameter.id,⟨before.cells.length⟩)::captured) after (.bool flag) := by
          rcases capturedValue with ⟨location,cell,lookup,read,ordinary,contents⟩
          exact ⟨location,cell,.tail shape.parameterFlag lookup,(Tests.SourceCoreMixedImperative.HeapAppends.read (show Tests.SourceCoreMixedImperative.HeapAppends before after from ⟨_,rfl⟩) read),ordinary,contents⟩
        have captureTrace := Tests.SourceCoreMixedImperative.read_value (program := program) (context := function.context.withLocal parameter.id parameter.scheme parameter.schemeRequirements) (evidence := evidence) (substituteRead shape.capture substitution) captureStored
        have zeroTrace := (substituteWord shape.zero substitution).evaluates (program := program) evidence
          ((parameter.id,⟨before.cells.length⟩)::captured) after frame.code.graph.nodeOccurrencesUnique zeroTyped
        have expression := (shape.result.substitute substitution).evaluates
          ((shape.duplicate.substitute substitution).evaluates firstTrace secondTrace)
          ((shape.extra.substitute substitution).evaluates captureTrace zeroTrace)
        apply Dynamic.CallableApplies.closure rfl frame extended
        · exact .cons allocation (.nil _ _)
        · apply Dynamic.FunctionStatementsExecute.singleton
            (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound))
          · intro expression impossible; rw [returnedForm] at impossible; cases impossible
          · apply Dynamic.StatementExecutes.returnValue
              (FlexibleSubstitution.ContainsStatement.applySubstitution substitution (lookupStatement?_sound shape.returnFound)) returnedForm
            simpa only [function,parameter,after,LambdaShape.descriptor,Dynamic.GeneralizedClosure.instantiate,Dynamic.GeneralizedClosure.ofDirectLambda,resultValue,PairAt.substitute,ExpressionNode.applySubstitution,substituteWord,IntegerLiteralResolution.applySubstitution_rawValue,shape.zeroValue] using expression
        · rfl

theorem LambdaShape.invoke {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (substitution : TypeSystem.Substitution)
    (evidence produced : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] substitution produced)
    (frame : Dynamic.ClosureFrame program
      ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution)))
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue argument flag) ⟨argumentsHeap.cells ++ [{type := (shape.parameter.applySubstitution substitution).scheme.body, value := some argument}]⟩ := by
  have callee : Dynamic.ExpressionEvaluates program context evidence source environment before
      call.callee.node.id
      (.closure ((shape.descriptor definitionContext captured).instantiate substitution
        (produced ++ evidence.applySubstitution substitution))) before := by
    apply Dynamic.ExpressionEvaluates.generalizedLocal (owned := [])
      (lookupExpression?_sound call.callee.found) call.callee.form
      (by rw [call.callee.requirements, call.callee.coercions]; rfl)
      lookup read descriptor fields
    · rw [call.callee.raw]; exact instantiation
    · rw [call.callee.coercions]; exact .nil
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound call.found)
  · rw [call.form]
    exact .indirectCall
      (by rw [call.requirements, call.argumentCoercions, call.coercions]; rfl)
      callee (.cons argumentTrace .nil) (.singleton argument)
      (by rw [call.argumentCoercions]; exact .nil) (.singleton argument)
      (by rw [call.arity]; rfl) (by rw [call.arity]; rfl)
      (shape.body_applies captured substitution _ evidence argumentsHeap argument flag capturedValue frame)
  · rw [call.coercions]; exact .nil


theorem LambdaShape.instance {source : TypedSource} (shape : LambdaShape source)
    {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
    {type : TypeSystem.Ty} (wellformed : SchemeWellFormed context shape.binder.scheme)
    (ground : TypeWellFormed context type) :
    Dynamic.LocalSchemeRuntimeInstantiation context evidence shape.binder
      (.function type (resultType type)) [] [(shape.typeVariable, type)] [] := by
  refine ⟨LocalSchemeRequirementsWellFormed.empty _ _ shape.schemeRequirements,
    wellformed, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · rw [shape.scheme]; exact ExactSubstitution.singleton _ _
  · intro typeVariable replacement member
    have same := List.mem_singleton.mp member
    cases same
    exact ground
  · simp [shape.scheme, TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?,resultType]
  · intro id member; cases member
  · rw [instantiateLocalSchemePredicates, shape.schemeRequirements]
    exact .nil


theorem LambdaShape.frame {source : TypedSource} (shape : LambdaShape source)
    {program : SourceSemantics.Program} {context nextContext : SourceSemantics.Context}
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (evidence : Dynamic.EvidenceEnvironment) {type : TypeSystem.Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.GeneralizedClosureWellTyped nextContext heap (shape.descriptor context environment))
    (fields : Dynamic.RuntimeContextFields context nextContext)
    (signatures : nextContext.signatures = program.signatures)
    (covers : evidence.Covers nextContext)
    (wellformed : SchemeWellFormed nextContext shape.binder.scheme)
    (ground : TypeWellFormed nextContext type) :
    Dynamic.ClosureFrame program
      ((shape.descriptor context environment).instantiate [(shape.typeVariable, type)]
        (evidence.applySubstitution [(shape.typeVariable, type)])) := by
  have materialized := Dynamic.GeneralizedClosureWellTyped.instantiateHasType
    catalog typed fields covers (shape.instance evidence wellformed ground)
  obtain ⟨_parameter, _result, same, code, closed, _captured⟩ := materialized.closure_function_inv
  exact ⟨same.trans signatures, code.owner, code, code.requirement_ledger.idsUnique, closed⟩


private theorem descriptor_scheme_of_typed
    {source : TypedSource} {context : SourceSemantics.Context}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? node.id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType source context node.id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function) :
    SchemeWellFormed context function.binder.scheme := by
  generalize outputEq : node.type = output at typed
  cases typed with
  | intro contains formTyped rawType _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at formTyped
    cases formTyped with
    | reference reference =>
      cases reference with
      | «local» schemeLookup _ valid =>
        have identity := locals.lookup_generalized schemeLookup lookup read descriptor
        cases valid with
        | intro _ formed _ _ _ _ _ _ _ => exact identity.2 ▸ formed


theorem LambdaShape.invoke_from_typed {source : TypedSource} (shape : LambdaShape source)
    {argumentId : ExpressionId} {type : TypeSystem.Ty}
    (call : CallShape source shape.binder argumentId type)
    {program : SourceSemantics.Program} {definitionContext context : SourceSemantics.Context}
    (captured environment : Dynamic.Environment) (evidence : Dynamic.EvidenceEnvironment) (flag : Bool)
    {before argumentsHeap : Dynamic.Heap} {argument : Dynamic.Value}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : ExpressionHasType source context call.callee.node.id call.callee.node.type)
    (ground : TypeWellFormed context type)
    (capturedValue : StoredValue shape.flag captured argumentsHeap (.bool flag))
    (lookup : Dynamic.Environment.LooksUp environment shape.binder.id location)
    (read : Dynamic.Heap.Reads before location cell)
    (descriptor : cell.generalized = some (shape.descriptor definitionContext captured))
    (fields : Dynamic.RuntimeContextFields definitionContext context)
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment
      before argumentId argument argumentsHeap) :
    Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id
      (resultValue argument flag) ⟨argumentsHeap.cells ++ [{type := (shape.parameter.applySubstitution [(shape.typeVariable, type)]).scheme.body, value := some argument}]⟩ := by
  have wellformed := descriptor_scheme_of_typed runtime.graph.nodeOccurrencesUnique
    call.callee.found call.callee.form typed locals lookup read descriptor
  have descriptorTyped := ((heapTyped cell read.member).generalized_inv descriptor).2
  have frame := shape.frame captured before evidence
    (by simpa only [fields.signatures] using catalog) descriptorTyped fields
    runtime.signatures covers wellformed ground
  exact shape.invoke call captured environment [(shape.typeVariable, type)] evidence [] flag capturedValue
    lookup read descriptor fields (shape.instance evidence wellformed ground) frame argumentTrace

end Tests.SourceCoreGeneralizedBodyExpression
