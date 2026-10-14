import Solcore.SourceSemantics.Staging.SelectedBodyPreservation
import Solcore.SourceSemantics.SelectedOperatorTypingCertificates

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- Typing belongs to the exact method selection whose body the registry enters. -/
def MethodBodiesTyped (program : Program) (registry : Registry) : Prop :=
  ∀ {context : Context} {evidence dictionary : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    {body : BodyInstance} {roots : List StatementId} {child : Scope},
    OperatorMethodSelected program context evidence traitName methodName requirements body dictionary →
    StatementRoots body.source.roots roots →
    registry.Closure (methodView body dictionary roots) child →
    TypedOperatorMethodSelected program context evidence traitName methodName requirements body dictionary

structure SelectedBodies (program : Program) (registry : Registry) : Prop where
  signatures : SignatureCatalogWellFormed program.signatures
  globals : GlobalBodiesTyped program registry
  methods : MethodBodiesTyped program registry

/-- Every outcome retains deep heap typing. Only success adds a value judgment. -/
structure OutcomePreserved (context : Context) (before after : Heap)
    (type : Ty) (outcome : Outcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  value_typed : ∀ value, outcome = .value value → ValueHasType context after value type

structure ValuesPreserved (context : Context) (before after : Heap)
    (types : List Ty) (outcome : ValuesOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  values_typed : ∀ values, outcome = .values values → ValuesHaveTypes context after values types

structure StatementsPreserved (context staticFinal runtimeFinal : Context)
    (before after : Heap) (type : Ty) (outcome : BodyOutcome) (completion : Prop := True) (allowed : Prop := True) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  returned : completion → ∀ value, outcome = .returned value → ValueHasType context after value type
  fallthrough : ∀ environment, outcome = .fallthrough environment →
    runtimeFinal = staticFinal ∧ EnvironmentAgrees after staticFinal.locals environment ∧ allowed

structure ItemsPreserved (context staticFinal runtimeFinal : Context)
    (before after : Heap) (outcome : ForItemsOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  done : ∀ environment, outcome = .done environment →
    runtimeFinal = staticFinal ∧ EnvironmentAgrees after staticFinal.locals environment

variable (program : Program) (registry : Registry)

def ExpressionAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {outcome : Outcome} {type : Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context id type →
    Size.Expression program registry size scope context environment before id outcome after →
    OutcomePreserved context before after type outcome

def ExpressionsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {ids : List ExpressionId} {outcome : ValuesOutcome} {types : List Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionsHaveTypes scope.source context ids types →
    Size.Expressions program registry size scope context environment before ids outcome after →
    ValuesPreserved context before after types outcome

def AppliesAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {source : TypedSource}
    {before after : Heap} {callable : Value} {arguments : List Value} {packed : Value}
    {outcome : Outcome} {parameter result : Ty},
    SourceRuntimeValid program context source → HeapWellTyped context before →
    ValueHasType context before callable (.function parameter result) →
    ValuesPack arguments packed → ValueHasType context before packed parameter →
    Size.Applies program registry size scope context before callable arguments outcome after →
    OutcomePreserved context before after result outcome

def StatementsAt (size : Nat) : Prop :=
  ∀ {mode : Bool} {scope : Scope} {context staticFinal runtimeFinal : Context}
    {environment : Dynamic.Environment} {before after : Heap} {ids : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementsHaveType scope.source control context ids staticFinal facts →
    Size.StatementsIn program registry mode size scope context environment before ids runtimeFinal outcome after →
    StatementsPreserved context staticFinal runtimeFinal before after control.returnType outcome
      (mode = true → BodyCompletes control.returnType facts) (facts.control.canFallthrough = true)

def RawFormAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    {rawType finalType : Ty} {plan : ExpressionRequirementPlan},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    (∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType) →
    ExpressionFormHasRawType scope.source context form rawType plan →
    ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions →
    Size.RawForm program registry size scope context environment before form requirements coercions outcome after →
    OutcomePreserved context before after rawType outcome

def CoercionStepAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap}
    {step : SourceInference.CoercionStep} {input : Value} {outcome : Outcome},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input step.source → CoercionStepValid context step →
    Size.CoercionStep program registry size scope context before step input outcome after →
    OutcomePreserved context before after step.target outcome

def CoercionPathAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap}
    {steps : List SourceInference.CoercionStep} {input : Value} {outcome : Outcome}
    {sourceType targetType : Ty},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input sourceType → CoercionPathValid context sourceType targetType steps →
    Size.CoercionPath program registry size scope context before steps input outcome after →
    OutcomePreserved context before after targetType outcome

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
