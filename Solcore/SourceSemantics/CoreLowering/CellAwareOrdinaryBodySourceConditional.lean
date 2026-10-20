import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceScopes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageConditionalSourceInversion

/-! Original Source conditions select the same branch. Actual expression
preservation excludes non-Boolean conditions and supplies the reached heap
for the selected body and any live suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
open Core Frontend SourceInference Staging.Recursive
open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {program : Program} {registry : Registry} {invocation : Scope}

private def typeHead : TypeSystem.Ty → TypeSystem.Ty
  | .application function _ => typeHead function
  | type => type

private theorem typeHead_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    typeHead (TypeSystem.Ty.applyMany head arguments) = typeHead head := by
  unfold TypeSystem.Ty.applyMany
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl

private theorem boolean_of_typed {context : SourceSemantics.Context} {heap value}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (typed : Dynamic.ValueHasType context heap value .bool) : Dynamic.BooleanValue value := by
  generalize typeEq : TypeSystem.Ty.bool = type at typed
  cases typed with
  | bool => trivial
  | unit => simp [TypeSystem.Ty.bool,TypeSystem.Ty.unit] at typeEq
  | word => simp [TypeSystem.Ty.bool,TypeSystem.Ty.word] at typeEq
  | integer => simp [TypeSystem.Ty.bool,TypeSystem.Ty.integer] at typeEq
  | product => cases typeEq
  | proxy => cases typeEq
  | mapping => cases typeEq
  | closure => cases typeEq
  | comptime => cases typeEq
  | builtin function => rw [BuiltinFunctionId.type] at typeEq; cases typeEq
  | constructed valid _ =>
      cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
          rw [resultType_eq] at typeEq
          have heads := congrArg typeHead typeEq
          simp [TypeSystem.Ty.nominal,typeHead_applyMany,typeHead,TypeSystem.Ty.bool] at heads
  | global valid _ =>
      cases valid with
      | intro signature member declaration_eq substitution_exact substitution_range instantiation_type_eq
          predicates_eq parameterComptime_eq returnComptime_eq =>
          have signatureValid := catalog.functions_semantic signature member
          rw [instantiation_type_eq,signatureValid.scheme_body] at typeEq
          cases typeEq

theorem conditional (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {reasonAt context scope mode id node condition conditionNode conditionCode thenBody elseBody rest}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : invocation.source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (certificate : CellAwareLexicalBodyExpressions.StaticCertificate checked invocation.source reasonAt context scope condition ⟨.bool,conditionCode⟩)
    (branches : ∀ truth : Bool, Lifts (program := program) (registry := registry) (invocation := invocation)
      context false (if truth then thenBody else elseBody.getD []))
    (remaining : Lifts (program := program) (registry := registry) (invocation := invocation) context mode rest ∨
      ∀ truth : Bool, GenericLexicalStatements.Stopped invocation.source (if truth then thenBody else elseBody.getD [])) :
    Lifts (program := program) (registry := registry) (invocation := invocation) context mode (id::rest) := by
  intro environment before state size finalContext outcome after trace
  have unique := state.runtime.graph.nodeOccurrencesUnique
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same; rw [form] at same; cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨_,reason,_,rfl,rfl,failed⟩ | ⟨_,_,stopped,executed⟩ | ⟨_,_,middleContext,nextEnvironment,middle,_,_,executed,tail⟩
  · rcases SelectedCompilationStageConditionalSourceInversion.fault unique found form failed with
      ⟨_,_,test⟩ | ⟨_,value,_,_,rfl,test,invalid,_⟩ | ⟨_,_,truth,_,_,_,_,test,branch⟩
    · exact ⟨.ifConditionFault (lookupStatement?_sound found) form (expression certificate unique (.fault test)),trivial⟩
    · obtain ⟨typed,_,_⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      rw [conditionType] at typed
      exact False.elim (invalid (boolean_of_typed (state.runtime.signatures.symm ▸ selectedBodies.signatures) typed))
    · have first := expression (registry := registry) certificate unique (.value test)
      obtain ⟨_,reached,_⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      obtain ⟨lifted,_⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .fault branch)
      exact ⟨.ifFault (lookupStatement?_sound found) form first lifted,trivial⟩
  · obtain ⟨_,_,truth,_,_,innerOutcome,_,_,sameContext,sameOutcome,test,branch⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique found form executed
    subst finalContext outcome
    have first := expression (registry := registry) certificate unique (.value test)
    obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
    obtain ⟨lifted,post⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control branch)
    cases innerOutcome with
    | returned value => exact ⟨.ifReturned (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | breaking innerEnvironment => exact ⟨.ifBreaking (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | continuing innerEnvironment => exact ⟨.ifContinuing (lookupStatement?_sound found) form first lifted,post.trans extension⟩
    | fault reason => exact ⟨.ifFault (lookupStatement?_sound found) form first lifted,trivial⟩
    | fallthrough innerEnvironment =>
      rcases stopped with impossible | rfl
      · cases impossible
      · exact ⟨.ifFallthrough (lookupStatement?_sound found) form first lifted .nil,post.trans extension⟩
  · obtain ⟨_,_,truth,_,_,innerOutcome,_,_,sameContext,restored,test,branch⟩ :=
      SelectedCompilationStageConditionalSourceInversion.control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl,Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      have first := expression (registry := registry) certificate unique (.value test)
      obtain ⟨_,reached,extension⟩ := expression_typed selectedBodies certificate conditionFound state (.value test)
      obtain ⟨lifted,post⟩ := branches truth reached (show PlainStatements program false _ invocation _ _ _ _ _ _ _ from .control branch)
      rcases remaining with remaining | stopped
      · have nextState : State (program := program) (invocation := invocation) context environment middle :=
          ⟨state.runtime,state.covers,state.locals.mono (extension.trans post.2),post.1⟩
        obtain ⟨restTrace,restPost⟩ := remaining nextState tail
        exact ⟨.ifFallthrough (lookupStatement?_sound found) form first lifted restTrace,
          restPost.trans (extension.trans post.2)⟩
      · have impossible := (stopped truth).terminates unique false branch.sound
        cases impossible
    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySourceState
