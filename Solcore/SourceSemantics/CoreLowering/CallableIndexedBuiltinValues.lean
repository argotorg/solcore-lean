import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.BuiltinCallCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityPayload
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes
import Solcore.SourceSemantics.Dynamic.Evaluation

/-! Builtin leaves for the real indexed artifact. Nonwrapping identities come
from its actual global prefix and the compiler builtin inventory. Descriptors
belong to that artifact's sealed codebook, while closures retain the actual
ambient-typed capture environment. The three payload laws follow from those
receipts without a function-body execution premise. Named and anonymous source
functions are outside this leaf model; no closure history is inferred here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    Dynamic.Value → Word → Prop where
  | builtin {function : BuiltinFunctionId} {index : Nat} {identity : Word}
      (selected : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity) :
      Identity prepared (.builtin ⟨function⟩) identity

private theorem word_value {number : Nat} {word : Word} (accepted : Word.ofNat? number = some word) :
    word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

/-- Equal IDs mean the complete source builtin identity is equal, in both
 directions. The global prefix is never reduced modulo the word size. -/
theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related; cases related; exact .builtin _
  · intro left right a b first second
    cases first with
    | @builtin f i a foundA numberA =>
      cases second with
      | @builtin g j b foundB numberB =>
        constructor
        · intro same
          have indices : i = j := by
            have values := (word_value numberA).symm.trans ((congrArg Fin.val same).trans (word_value numberB))
            omega
          have itemA := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some foundA)
          have itemB := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some foundB)
          have functions : f = g := Option.some.inj (itemA.symm.trans (indices ▸ itemB))
          cases functions
          rfl
        · intro same
          have functions : f = g := by cases same; rfl
          subst g
          have indices : i = j := (Prod.mk.inj (Option.some.inj (foundA.symm.trans foundB))).2
          exact Option.some.inj (numberA.symm.trans (indices ▸ numberB))

/-- Builtin IDs remain outside every named global slot of the same artifact. -/
theorem Identity.outside_globals {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : Dynamic.Value} {identity named : Word} {position : Nat}
    (related : Identity prepared source identity) (bound : position < prepared.base.globals.length)
    (selected : Word.ofNat? (position + 1) = some named) : identity ≠ named := by
  intro same
  cases related with
  | builtin _ number =>
    have index := (word_value number).symm.trans ((congrArg Fin.val same).trans (word_value selected))
    omega

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {function : BuiltinFunctionId} {index : Nat} {identity : Word}
      {captured : Environment} {context : Core.Context}
      (selected : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity)
      (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function))
      (typed : RuntimeEnvironmentHasTypes world captured context prepared.layouts.definitions) :
      Represents prepared world function.type (.builtin ⟨function⟩)
        (BuiltinCalls.Protocol.contractedValue function identity descriptor.id captured)
        (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))

private theorem projected {catalog : SourceCoreCompatibleCatalog.Catalog}
    (profile : catalog.callableContracts = true) (function : BuiltinFunctionId) :
    catalog.project function.type = .ok
      (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)) := by
  cases function <;> simp [BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes, BuiltinFunctionId.returnType,
    TypeSystem.Ty.productMany, TypeSystem.Ty.integer, TypeSystem.Ty.word, TypeSystem.Ty.bool, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreCompatibleCatalog.Catalog.functionType,
    profile, SourceCoreInteger.builtinParameter, SourceCoreInteger.builtinResult]

theorem Represents.runtime_hasType {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) :
    RuntimeValueHasType world value type prepared.layouts.definitions := by
  cases related with
  | @builtin function index identity captured context selected number descriptor typed =>
    have body := SourceCoreInteger.builtinClosure_hasType (scope := context) (definitions := prepared.layouts.definitions) function
    cases body with
    | lambda _ _ body => exact .pair (.pair (.inRight .word) (.closure typed body)) .word

/-- The ambient environment is the actual frame/marker suffix, not a catalog
with administrative entries assigned fabricated source types. -/
def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by intro _ _ _ _ _ _ _ related; cases related; exact projected profile _
  runtime_hasType := Represents.runtime_hasType
  source_function := by intro _ _ _ _ _ _ _ related; cases related; exact .builtin _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related _ _ worlds
    cases related with
    | builtin selected number descriptor typed => exact .builtin selected number descriptor (typed.weaken worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | builtin selected number descriptor _ =>
    exact .contractedIdentified _ _ _ descriptor.id (.builtin selected number) profile

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ parameter result source value type related
  cases related
  exact (Dynamic.ValueRuntimeType.builtin _).matches

/-- Successful actual builtin-reference lowering authenticates inventory,
source header and the artifact descriptor before forming the real closure.
No evidence resolver or source evaluator is executed by this proof. -/
theorem formation_of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
      compilation source node name function = .ok lowered)
    {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    (store : Store) (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type := by
  have reference := BuiltinCalls.reference_of_accepted accepted
  cases reference with
  | @intro index identity expression spelling sourceType inventory identitySelected decorated =>
    cases descriptorFound : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function) with
    | error error =>
      simp [SourceCoreGeneralFunctions.callablePolicy, descriptorFound, bind, Except.bind, Except.mapError] at decorated
    | ok descriptor =>
      have emitted := ActualCallablePolicy.builtin_decoration prepared.ancestry.graph.inputs.callable active compilation source node
        function (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)) descriptor
      have same := Except.ok.inj (emitted.symm.trans decorated)
      subst expression
      refine ⟨BuiltinCalls.Protocol.contractedValue function identity descriptor.id actual, ?_, ?_⟩
      · exact BuiltinCalls.Protocol.contracted_evaluates function identity descriptor.id actual store
      · rw [sourceType]
        exact .builtin inventory (by simpa only [globals] using identitySelected) descriptor typed


/-- Every completed evaluation of the actual reference has the authenticated
value and leaves the entire store unchanged, including administrative cells. -/
theorem reference_reflects {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
      compilation source node name function = .ok lowered)
    {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)
    {store finalStore : Store} {result : Value}
    (completed : Evaluates actual store lowered.expression result finalStore)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, result = .inRight .word value ∧ finalStore = store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type := by
  obtain ⟨value, evaluated, related⟩ := formation_of_accepted prepared profile globals accepted typed store registry mapping
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨value, same, stores, related⟩

/-- At a real ordinary source occurrence, the same value is produced by the
independent source rule. Source requirement/coercion admission remains explicit. -/
theorem source_reference (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (name : String) (function : BuiltinFunctionId)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id (.builtin ⟨function⟩) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form, requirements, coercions]
    exact .builtinFunction rfl
  · rw [coercions]; exact .nil

end Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
