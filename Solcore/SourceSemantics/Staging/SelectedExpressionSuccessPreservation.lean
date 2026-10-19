import Solcore.SourceSemantics.Staging.SelectedRawPreservation
import Solcore.SourceSemantics.Staging.SelectedMethodPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

private theorem empty_path_type {context : Context} {source target : Ty}
    (path : CoercionPathValid context source target []) : source = target := by
  cases path
  rfl

private theorem expression_form_exact {scope : Scope} {context : Context} {id : ExpressionId}
    {form : ExpressionForm} {type : Ty} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique scope.source)
    (typed : ExpressionHasType scope.source context id type) (occurrence : Occurrence scope id form requirements) :
    ∃ plan, ExpressionFormHasRawType scope.source context form type plan ∧
      ExpressionRequirementPlan.Valid context type type plan requirements [] := by
  obtain ⟨raw, plan, formTyped, valid⟩ := FaultPreservation.expression_form_plan unique typed occurrence
  have equal := empty_path_type valid.outputPath
  subst raw
  exact ⟨plan, formTyped, valid⟩

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

theorem expression_value_step (selectedBodies : SelectedBodies program registry) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (rawIH : ∀ smaller, smaller < size → RawFormAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller)
    {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {value : Value} {type : Ty}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (typed : ExpressionHasType scope.source context id type)
    (trace : Size.Expression program registry size scope context environment before id (.value value) after) :
    ExpressionEvaluationPreserved context before after value type := by
  cases trace with
  | @atomicValue scope context environment before after id node value contains atomic uncoerced valueRule =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have post := atomic_value runtime covers locals heap ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm atomic valueRule
          have path := valid.outputPath
          rw [uncoerced] at path
          exact ⟨empty_path_type path ▸ post.value_typed, post.heap_typed, post.heap_extends⟩
  | @coercedValue rawSize pathSize scope context environment before middle after id node value outcome contains _nonempty raw path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have rawPost := rawIH rawSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
            ⟨id, node, contains, rfl, rawTypeEq⟩ typedForm valid raw
          have post := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime rawPost.heap_typed (rawPost.value_typed _ rfl) valid.outputPath path
          exact ⟨post.value_typed _ rfl, post.heap_typed, rawPost.heap_extends.trans post.heap_extends⟩
  | @generalizedLocal pathSize scope context environment before after id node name binder owned
      location cell function substitution produced outcome contains _form _layout _lookup read descriptor contextFields instantiation path =>
      cases typed with
      | @intro _ _ actual rawType plan typedContains _typedForm rawTypeEq _ _ valid =>
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst actual
          have cellTyped := heap cell read.member
          have functionTyped := (cellTyped.generalized_inv descriptor).2
          have definitionCatalog : SignatureCatalogWellFormed function.definitionContext.signatures := by
            rw [← contextFields.signatures, runtime.signatures]
            exact selectedBodies.signatures
          have rawTyped := functionTyped.instantiateHasType definitionCatalog contextFields covers instantiation
          rw [rawTypeEq] at rawTyped
          have post := pathIH pathSize (Size.child_lt_stepSize (by simp))
            runtime heap rawTyped valid.outputPath path
          exact ⟨post.value_typed _ rfl, post.heap_typed, post.heap_extends⟩
  | @group childSize scope context environment before after id inner outcome occurrence child =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | group innerTyped =>
          exact expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap innerTyped child
  | @pair firstSize secondSize scope context environment before middle after id left right a b occurrence first second =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped restTyped =>
              cases restTyped with
              | cons secondTyped nilTyped =>
                  cases nilTyped
                  have leftPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap firstTyped first
                  have rightPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono leftPost.heap_extends) leftPost.heap_typed secondTyped second
                  exact ⟨.product ((leftPost.value_typed _ rfl).mono rightPost.heap_extends) (rightPost.value_typed _ rfl),
                    rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
  | @tupleValue childrenSize scope context environment before after id elements values packed occurrence children pack =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap elementsTyped children
          exact ⟨pack.hasType (post.values_typed _ rfl), post.heap_typed, post.heap_extends⟩
  | @constructorValue childrenSize scope context environment before after id instantiation arguments values occurrence valid children =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | constructor _valid argumentsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          exact ⟨.constructed valid (post.values_typed _ rfl), post.heap_typed, post.heap_extends⟩
  | @indexResult firstSize secondSize scope context environment before middle after id base key baseValue keyValue outcome occurrence first second result =>
      obtain ⟨_plan, formTyped, _valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | index baseTyped keyTyped =>
          have leftPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap baseTyped first
          have rightPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono leftPost.heap_extends) leftPost.heap_typed keyTyped second
          have baseAfter := (leftPost.value_typed _ rfl).mono rightPost.heap_extends
          cases result with
          | found shape located =>
              subst baseValue
              obtain ⟨rfl, rfl, entriesTyped⟩ := baseAfter.mappingComponents
              exact ⟨located.preserves entriesTyped, rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
          | default shape _absent defaulted =>
              subst baseValue
              obtain ⟨rfl, rfl, _entriesTyped⟩ := baseAfter.mappingComponents
              exact ⟨defaulted.hasType, rightPost.heap_typed, leftPost.heap_extends.trans rightPost.heap_extends⟩
  | @unary childSize scope context environment before after id operator operand input output occurrence child applies =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases valid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirementsEq
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap operandTyped child
              cases operatorTyped with
              | logicalNot => exact ⟨applies.preserves .logicalNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | wordBitNot => exact ⟨applies.preserves .wordBitNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | integerBitNot => exact ⟨applies.preserves .integerBitNot (post.value_typed _ rfl), post.heap_typed, post.heap_extends⟩
              | trait _dispatch profile requirementsProve => cases requirementsProve; cases profile
  | @binaryShortCircuit firstSize scope context environment before after id left operator right input output occurrence first circuit =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _rightTyped operatorTyped =>
          have post := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap leftTyped first
          cases circuit <;> cases operatorTyped
          all_goals try { rename_i kind; cases kind }
          all_goals try { rename_i dispatch profile proof; cases dispatch }
          all_goals exact ⟨.bool _, post.heap_typed, post.heap_extends⟩
  | @binary firstSize secondSize scope context environment before middle after id left operator right a b output occurrence first _continues second applies =>
      obtain ⟨_plan, formTyped, valid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases valid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirementsEq
              have firstPost := expressionIH firstSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap leftTyped first
              have secondPost := expressionIH secondSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono firstPost.heap_extends) firstPost.heap_typed rightTyped second
              have aTyped := (firstPost.value_typed _ rfl).mono secondPost.heap_extends
              have bTyped := secondPost.value_typed _ rfl
              cases operatorTyped with
              | wordArithmetic kind => exact ⟨applies.preserves (.wordArithmetic kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | integerArithmetic kind => exact ⟨applies.preserves (.integerArithmetic kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | wordComparison kind => exact ⟨applies.preserves (.wordComparison kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | integerComparison kind => exact ⟨applies.preserves (.integerComparison kind) aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | booleanAnd => exact ⟨applies.preserves .booleanAnd aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | booleanOr => exact ⟨applies.preserves .booleanOr aTyped bTyped, secondPost.heap_typed, firstPost.heap_extends.trans secondPost.heap_extends⟩
              | trait _dispatch profile requirementsProve => cases requirementsProve; cases profile
  | @unaryMethod operandSize bodySize scope context environment before argumentsHeap bound after id operator operand input
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_plan, formTyped, planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨inputTyped, argumentsHeapTyped, operandExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap operandTyped operandTrace
              cases operatorTyped with
              | logicalNot | wordBitNot | integerBitNot => cases method
              | trait staticDispatch profile requirementsProve =>
                  have same := unary_dispatch_same staticDispatch dispatch
                  rcases same with ⟨rfl, rfl⟩
                  obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
                    (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                      profile requirementsProve
                  have argumentsTyped := ValuesHaveTypes.cons inputTyped (.nil)
                  obtain ⟨resultTyped, afterTyped, bodyExtends⟩ := body_success
                    (StatementsAt.bodySuccess (statementsIH bodySize (Size.child_lt_stepSize (by simp)))) runtime certificate
                    (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                  exact ⟨(by simpa [resultEq, Ty.productMany] using resultTyped), afterTyped, operandExtends.trans bodyExtends⟩
  | @binaryMethod leftSize rightSize bodySize scope context environment before middle argumentsHeap bound after id left operator right a b
      requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result
      occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨_plan, formTyped, planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped operatorTyped =>
          cases planValid with
          | ordinary _ _ requirementsEq =>
              simp [coercionRequirementIds] at requirementsEq
              subst requirements
              obtain ⟨leftValueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers locals heap leftTyped first
              obtain ⟨rightValueTyped, argumentsHeapTyped, secondExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono firstExtends) middleTyped rightTyped second
              cases operatorTyped with
              | wordArithmetic | integerArithmetic | wordComparison | integerComparison | booleanAnd | booleanOr => cases method
              | trait staticDispatch profile requirementsProve =>
                have same := binary_dispatch_same staticDispatch dispatch
                rcases same with ⟨rfl, rfl⟩
                obtain ⟨lexicalContext, facts, certificate, resultEq⟩ :=
                  (selectedBodies.methods method rootsEq selected).certificateOfProfile selectedBodies.signatures runtime.signatures runtime.requirements.idsUnique
                    profile requirementsProve
                have argumentsTyped := ValuesHaveTypes.cons (leftValueTyped.mono secondExtends)
                  (.cons rightValueTyped (.nil))
                obtain ⟨resultTyped, afterTyped, bodyExtends⟩ := body_success
                  (StatementsAt.bodySuccess (statementsIH bodySize (Size.child_lt_stepSize (by simp)))) runtime certificate
                  (by cases method; assumption) argumentsHeapTyped argumentsTyped rootsEq selected parameters allocate body resultRule
                exact ⟨(by simpa [resultEq, Ty.productMany] using resultTyped), afterTyped, firstExtends.trans (secondExtends.trans bodyExtends)⟩
  | @conditional testSize branchSize scope context environment before middle after id condition yes no truth outcome
      occurrence test branch =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped yesTyped noTyped =>
          obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap conditionTyped test
          have branchTyped : ExpressionHasType scope.source context (if truth then yes else no) type := by
            split <;> assumption
          obtain ⟨resultTyped, afterTyped, branchExtends⟩ := expression_value (expressionIH branchSize (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono testExtends) middleTyped branchTyped branch
          exact ⟨resultTyped, afterTyped, testExtends.trans branchExtends⟩
  | @builtinApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments function values outcome occurrence children invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          have calleeTyped : ValueHasType context argumentsHeap (.builtin ⟨function⟩)
              (.function (TypeSystem.Ty.productMany function.parameterTypes) function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap) ⟨function⟩)
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have argumentTyped := packing.hasType valuesTyped
          have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
            runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
          exact ⟨post.value_typed _ rfl, post.heap_typed, argumentExtends.trans post.heap_extends⟩
  | @directApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments instantiation name values evidence outcome requirements occurrence _calleeOccurrence valid children callEvidence invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) type) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨post.value_typed _ rfl, post.heap_typed, argumentExtends.trans post.heap_extends⟩
  | @applied childSize childrenSize invocationSize scope context environment before calleeHeap argumentsHeap after
      id callee arguments metadata value values outcome occurrence uncoerced child _guard children _arity invocation =>
      obtain ⟨_plan, formTyped, _planValid⟩ := expression_form_exact runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped application =>
          obtain ⟨valueTyped, calleeHeapTyped, calleeExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap calleeTyped child
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values (expressionsIH _ (Size.child_lt_stepSize (by simp)))
            runtime covers (locals.mono calleeExtends) calleeHeapTyped argumentsTyped children
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have packedTyped := packing.hasType valuesTyped
          cases application with
          | intro _count beforeEq _afterEq path =>
              rw [uncoerced] at path
              rw [← beforeEq] at packedTyped
              have argumentTyped := empty_path_type path ▸ packedTyped
              have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                runtime argumentsHeapTyped (valueTyped.mono argumentExtends) packing argumentTyped invocation
              exact ⟨post.value_typed _ rfl, post.heap_typed, calleeExtends.trans (argumentExtends.trans post.heap_extends)⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
