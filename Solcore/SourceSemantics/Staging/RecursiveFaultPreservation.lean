import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationApplies
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationStatements

/-! Faulting recursive staged executions preserve deep Source heap typing.
The numeric induction follows actual faulting children; successful prefixes use
their independent whole-language preservation and retain all executed effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

private theorem empty_path_type {context : Context} {source target : Ty}
    (path : CoercionPathValid context source target []) : source = target := by
  cases path
  rfl

private theorem expressions_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller) :
    ExpressionsAt program registry size := by
  intro scope context environment before after ids failure types runtime covers locals heap typed trace
  cases trace with
  | @headFault headSize scope context environment before after id ids failure head =>
      cases typed with
      | cons headTyped _ =>
          exact expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
  | @tailFault headSize tailSize scope context environment before middle after id ids value failure head tail =>
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap headTyped head
          obtain ⟨afterTyped, tailExtends⟩ := expressionsIH tailSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped tail
          exact ⟨afterTyped, headExtends.trans tailExtends⟩

private theorem unary_dispatch_same
    {operator : Syntax.UnaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right
  exact ⟨rfl, rfl⟩

private theorem binary_dispatch_same
    {operator : Syntax.BinaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait ∧ leftMethod = rightMethod := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

private theorem raw_form_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller) :
    RawFormAt program registry size := by
  intro scope context environment before after form requirements coercions failure rawType finalType plan
    runtime covers locals heap _occurrence typed _valid trace
  cases trace with
  | rawAtomicFault atomic faultRule =>
      have same := atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _⟩
  | @rawDirectArgumentsFault childrenSize scope context environment before after callee arguments instantiation name failure requirements coercions _calleeOccurrence children =>
      cases typed with
      | directCall _calleeTyped _application argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
  | @rawDirectApplied childrenSize invocationSize scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions _calleeOccurrence valid children callEvidence invocation =>
      cases typed with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) rawType) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩

private theorem coercion_step_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    CoercionStepAt program registry size := by
  intro scope context before after step input failure runtime heap typed valid trace
  cases trace with
  | coercionRequirement _ | coercionPrimitiveInput _ _ _ => exact ⟨heap, .refl _⟩
  | @coercionMethod bodySize scope context before bound after step input bodyInstance dictionary roots child
      parameterTypes bodyContext finalContext bodyEnvironment outcome result method rootsEq selected parameters allocate body resultRule =>
      cases valid with
      | intro profile requirementsProve =>
          obtain ⟨lexicalContext, facts, certificate, _resultEq⟩ :=
            method.coercionCertificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique profile requirementsProve
          exact method_body_fault
            (statementsIH bodySize (Size.child_lt_stepSize (by simp))) runtime certificate
            (by cases method; assumption) heap (.cons typed .nil) rootsEq selected parameters allocate body resultRule

private theorem coercion_path_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (stepIH : ∀ smaller, smaller < size → CoercionStepAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    CoercionPathAt program registry size := by
  intro scope context before after steps input failure sourceType targetType runtime heap typed valid trace
  cases trace with
  | @coercionsFault headSize scope context before after step steps input failure head =>
      cases valid with
      | cons headValid _ =>
          exact stepIH headSize (Size.child_lt_stepSize (by simp)) runtime heap typed headValid head
  | @coercionsCons headSize tailSize scope context before middle after step steps input converted outcome head tail =>
      cases valid with
      | cons headValid tailValid =>
          obtain ⟨convertedTyped, middleTyped, headExtends⟩ := coercion_step_value wellFormed runtime heap typed headValid head
          obtain ⟨afterTyped, tailExtends⟩ := pathIH tailSize (Size.child_lt_stepSize (by simp)) runtime middleTyped convertedTyped tailValid tail
          exact ⟨afterTyped, headExtends.trans tailExtends⟩

private theorem expression_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    ExpressionAt program registry size := by
  intro scope context environment before after id failure type runtime covers locals heap typed trace
  cases trace with
  | generalizedLocalRequirement => exact ⟨heap, .refl _⟩
  | @generalizedLocal pathSize scope context environment before after id node name binder owned location cell function
      substitution produced outcome contains form layout lookup read descriptor contextFields instantiation coercions =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have functionTyped := ((heap cell read.member).generalized_inv descriptor).2
          have catalog : SignatureCatalogWellFormed function.definitionContext.signatures := by
            simpa only [functionTyped.same_signatures, runtime.signatures] using wellFormed.signatures
          have rawTyped := functionTyped.instantiateHasType catalog contextFields covers instantiation
          rw [rawTypeEq] at rawTyped
          exact pathIH pathSize (Size.child_lt_stepSize (by simp)) runtime heap rawTyped valid.outputPath coercions
  | @coercedFault rawSize scope context environment before after id node failure contains _nonempty raw =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          exact rawIH rawSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
  | @coercedValue rawSize pathSize scope context environment before middle after id node value outcome contains _nonempty raw path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          obtain ⟨valueTyped, middleTyped, rawExtends⟩ := raw_form_value wellFormed runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
          obtain ⟨afterTyped, pathExtends⟩ := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime middleTyped valueTyped valid.outputPath path
          exact ⟨afterTyped, rawExtends.trans pathExtends⟩
  | atomicFault _ atomic _ faultRule =>
      have same := atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _⟩
  | @group childSize scope context environment before after id inner outcome occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | group innerTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped child
  | @pairLeftFault childSize scope context environment before after id left right failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap firstTyped child
  | @pairRightFault firstSize secondSize scope context environment before middle after id left right value failure
      occurrence first second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped restTyped =>
              cases restTyped with
              | cons secondTyped _ =>
                  obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
                    runtime covers locals heap firstTyped first
                  obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
                    runtime covers (locals.mono firstExtends) middleTyped secondTyped second
                  exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @tupleFault childrenSize scope context environment before after id elements failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap elementsTyped children
  | @constructorFault childrenSize scope context environment before after id instantiation arguments failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | constructor _valid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @indexBaseFault firstSize scope context environment before after id base key failure occurrence first =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped _ =>
          exact expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap baseTyped first
  | @indexKeyFault firstSize secondSize scope context environment before middle after id base key value failure occurrence first second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed runtime covers locals heap baseTyped first
          obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono firstExtends) middleTyped keyTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @indexResult firstSize secondSize scope context environment before middle after id base key baseValue keyValue outcome occurrence first second _result =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          obtain ⟨_baseTyped, middleTyped, firstExtends⟩ := expression_value wellFormed runtime covers locals heap baseTyped first
          obtain ⟨_keyTyped, afterTyped, secondExtends⟩ := expression_value wellFormed
            runtime covers (locals.mono firstExtends) middleTyped keyTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @unaryOperandFault childSize scope context environment before after id operator operand failure requirements occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap operandTyped child
  | @unaryInvalid childSize scope context environment before after id operator operand input occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap operandTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @binaryLeftFault firstSize scope context environment before after id left operator right failure requirements occurrence first =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          exact expressionIH firstSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap leftTyped first
  | @binaryLeftInvalid firstSize scope context environment before after id left operator right input occurrence first _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          exact ⟨afterTyped, heapExtends⟩
  | @binaryRightFault firstSize secondSize scope context environment before middle after id left operator right input failure requirements
      occurrence first _continues second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @binaryInvalid firstSize secondSize scope context environment before middle after id left operator right a b
      occurrence first _continues second _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_firstTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          obtain ⟨_secondTyped, afterTyped, secondExtends⟩ := expression_value wellFormed
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @unaryMethod operandSize bodySize scope context environment before argumentsHeap bound after id operator operand input
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_raw, _plan, formTyped, planValid⟩ := expression_form_plan runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨inputTyped, argumentsHeapTyped, operandExtends⟩ := expression_value wellFormed
                runtime covers locals heap operandTyped operandTrace
              cases operatorTyped with
              | logicalNot | wordBitNot | integerBitNot => cases method
              | trait staticDispatch profile requirementsProve =>
                  have same := unary_dispatch_same staticDispatch dispatch
                  rcases same with ⟨rfl, rfl⟩
                  obtain ⟨lexicalContext, facts, certificate, _resultEq⟩ :=
                    method.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique
                      profile requirementsProve
                  have argumentsTyped := ValuesHaveTypes.cons inputTyped (.nil)
                  obtain ⟨afterTyped, bodyExtends⟩ := method_body_fault
                    (statementsIH bodySize (Size.child_lt_stepSize (by simp))) runtime certificate
                    (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                  exact ⟨afterTyped, operandExtends.trans bodyExtends⟩
  | @binaryMethod leftSize rightSize bodySize scope context environment before middle argumentsHeap bound after id left operator right a b
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_raw, _plan, formTyped, planValid⟩ := expression_form_plan runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨leftValueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
                runtime covers locals heap leftTyped first
              obtain ⟨rightValueTyped, argumentsHeapTyped, secondExtends⟩ := expression_value wellFormed
                runtime covers (locals.mono firstExtends) middleTyped rightTyped second
              cases operatorTyped with
              | wordArithmetic | integerArithmetic | wordComparison | integerComparison | booleanAnd | booleanOr => cases method
              | trait staticDispatch profile requirementsProve =>
                have same := binary_dispatch_same staticDispatch dispatch
                rcases same with ⟨rfl, rfl⟩
                obtain ⟨lexicalContext, facts, certificate, _resultEq⟩ :=
                  method.certificateOfProfile wellFormed runtime.signatures runtime.requirements.idsUnique
                    profile requirementsProve
                have argumentsTyped := ValuesHaveTypes.cons (leftValueTyped.mono secondExtends)
                  (.cons rightValueTyped (.nil))
                obtain ⟨afterTyped, bodyExtends⟩ := method_body_fault
                  (statementsIH bodySize (Size.child_lt_stepSize (by simp))) runtime certificate
                  (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                exact ⟨afterTyped, firstExtends.trans (secondExtends.trans bodyExtends)⟩
  | @conditional testSize branchSize scope context environment before middle after id condition yes no truth outcome
      occurrence test branch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped yesTyped noTyped =>
          obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
            runtime covers locals heap conditionTyped test
          have branchTyped : ExpressionHasType scope.source context (if truth then yes else no) _raw := by
            split <;> assumption
          obtain ⟨afterTyped, branchExtends⟩ := expressionIH branchSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono testExtends) middleTyped branchTyped branch
          exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @conditionalFault testSize scope context environment before after id condition yes no failure occurrence test =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped _ _ =>
          exact expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
  | @builtinArgumentsFault childrenSize scope context environment before after id callee arguments function failure
      occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @builtinApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments function values outcome occurrence children invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers locals heap argumentsTyped children
          have calleeTyped : ValueHasType context argumentsHeap (.builtin ⟨function⟩)
              (.function (TypeSystem.Ty.productMany function.parameterTypes) function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap) ⟨function⟩)
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have argumentTyped := packing.hasType valuesTyped
          obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
            runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
          exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @directArgumentsFault childrenSize scope context environment before after id callee arguments instantiation name failure requirements
      occurrence _calleeOccurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | directCall _calleeTyped _application argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @directApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments instantiation name values evidence outcome requirements occurrence _calleeOccurrence valid children callEvidence invocation =>
      obtain ⟨raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) raw) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @calleeFault childSize scope context environment before after id callee arguments metadata failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap calleeTyped child
  | @notCallable childSize scope context environment before after id callee arguments metadata value occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @rejected childSize scope context environment before after id callee arguments metadata value reason occurrence child _guard =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @argumentsFault childSize childrenSize scope context environment before middle after id callee arguments metadata value failure
      occurrence child _guard children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨afterTyped, argumentExtends⟩ := expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @sourceArity childSize childrenSize scope context environment before middle after id callee arguments metadata value values
      occurrence child _guard children _mismatch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨_valuesTyped, afterTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @applied childSize childrenSize invocationSize scope context environment before calleeHeap argumentsHeap after
      id callee arguments metadata value values outcome occurrence uncoerced child _guard children _arity invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped application =>
          obtain ⟨valueTyped, calleeHeapTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers (locals.mono calleeExtends) calleeHeapTyped argumentsTyped children
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have packedTyped := packing.hasType valuesTyped
          cases application with
          | intro _count beforeEq _afterEq path =>
              rw [uncoerced] at path
              rw [← beforeEq] at packedTyped
              have argumentTyped := empty_path_type path ▸ packedTyped
              obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                runtime argumentsHeapTyped (valueTyped.mono argumentExtends) packing argumentTyped invocation
              exact ⟨afterTyped, calleeExtends.trans (argumentExtends.trans invocationExtends)⟩

private structure PreservedAt (program : Program) (registry : Registry) (size : Nat) : Prop where
  expression : ExpressionAt program registry size
  expressions : ExpressionsAt program registry size
  applies : AppliesAt program registry size
  statements : StatementsAt program registry size
  whileLoop : WhileAt program registry size
  matchArms : MatchAt program registry size
  forItems : ForItemsAt program registry size
  forLoop : ForLoopAt program registry size
  rawForm : RawFormAt program registry size
  coercionStep : CoercionStepAt program registry size
  coercionPath : CoercionPathAt program registry size

private theorem all (wellFormed : ProgramWellFormed program) (size : Nat) :
    PreservedAt program registry size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      exact {
        expression := expression_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).expressions)
          (fun smaller below => (ih smaller below).applies)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).rawForm)
          (fun smaller below => (ih smaller below).coercionPath)
        expressions := expressions_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).expressions)
        applies := applies_step wellFormed size
          (fun smaller below => (ih smaller below).statements)
        statements := statements_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).whileLoop)
          (fun smaller below => (ih smaller below).matchArms)
          (fun smaller below => (ih smaller below).forItems)
          (fun smaller below => (ih smaller below).forLoop)
        whileLoop := while_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).whileLoop)
        matchArms := match_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
        forItems := for_items_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).forItems)
        forLoop := for_loop_step wellFormed size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).forItems)
          (fun smaller below => (ih smaller below).forLoop)
        rawForm := raw_form_step wellFormed size
          (fun smaller below => (ih smaller below).expressions)
          (fun smaller below => (ih smaller below).applies)
        coercionStep := coercion_step_step wellFormed size
          (fun smaller below => (ih smaller below).statements)
        coercionPath := coercion_path_step wellFormed size
          (fun smaller below => (ih smaller below).coercionStep)
          (fun smaller below => (ih smaller below).coercionPath)
      }

/-- Any supported staged expression fault retains a deeply typed heap and all
heap type identities from its initial state. -/
theorem expression (wellFormed : ProgramWellFormed program) {size : Nat} :
    ExpressionAt program registry size := (all wellFormed size).expression

/-- Ordered expression faults retain every successful prefix's effects. -/
theorem expressions (wellFormed : ProgramWellFormed program) {size : Nat} :
    ExpressionsAt program registry size := (all wellFormed size).expressions

/-- Callable faults preserve the original caller's heap typing, including
faults raised by a recursively selected global or closure body. -/
theorem applies (wellFormed : ProgramWellFormed program) {size : Nat} :
    AppliesAt program registry size := (all wellFormed size).applies

/-- Faulting bodies preserve the original entry context and every executed
initializer and allocation prefix. -/
theorem statements (wellFormed : ProgramWellFormed program) {size : Nat} :
    StatementsAt program registry size := (all wellFormed size).statements

/-- Header faults preserve the initial heap typing across every visited item. -/
theorem for_items (wellFormed : ProgramWellFormed program) {size : Nat} :
    ForItemsAt program registry size := (all wellFormed size).forItems

/-- Finite for faults retain all real iteration and post-header effects. -/
theorem for_loop (wellFormed : ProgramWellFormed program) {size : Nat} :
    ForLoopAt program registry size := (all wellFormed size).forLoop

theorem raw_form (wellFormed : ProgramWellFormed program) {size : Nat} :
    RawFormAt program registry size := (all wellFormed size).rawForm

theorem coercion_step (wellFormed : ProgramWellFormed program) {size : Nat} :
    CoercionStepAt program registry size := (all wellFormed size).coercionStep

theorem coercion_path (wellFormed : ProgramWellFormed program) {size : Nat} :
    CoercionPathAt program registry size := (all wellFormed size).coercionPath

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
