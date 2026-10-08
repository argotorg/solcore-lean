import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping

/-! The actual successful callee representation and complete selected Code
identify only native callable parameter/result types. Authentic independent
binder projections then identify that same Code's packed binder type. An
arbitrary callable or binder policy supplies neither projection law. Original
raw Source bundles, genuine counts, body Syntax and stage gates stay separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
open Core Frontend SourceInference GeneralHeap CompatiblePayload CallableIndexedLambdaValues

/-- The original native callable wrapper retains both type parameters. -/
theorem callable_parameters {leftParameter leftResult rightParameter rightResult : Ty}
    (same : CallableContract.functionType leftParameter leftResult =
      CallableContract.functionType rightParameter rightResult) :
    leftParameter = rightParameter ∧ leftResult = rightResult := by
  have tagged := (Ty.product.inj same).1
  have function := (Ty.product.inj tagged).2
  have parameters := Ty.function.inj function
  exact ⟨parameters.1, (Ty.sum.inj parameters.2).2⟩

/-- Each genuine binder projection keeps the original ordered packed product.
This is a static list proof; no projection is recovered from a native value. -/
theorem binding_projection_pack {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings,
      checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := projected binding (by simp)
    cases rest with
    | nil => exact head
    | cons next tail =>
      have remainder := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, remainder]
      rfl

/-- The complete Code's actual Source signature and real binder row fix its
native bundle when both independent canonical projections are retained. -/
theorem code_binding_pack {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative)
    (profile : checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ code.receipt.loweredParameters,
      checked.catalog.project binding.1.scheme.body = .ok binding.2)
    (resultProjected : checked.catalog.project function.resultType = .ok code.receipt.resultCore) :
    code.receipt.parameterCore = SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) := by
  have packed := binding_projection_pack code.receipt.loweredParameters projected
  have parameters : function.parameters = code.receipt.loweredParameters.map Prod.fst :=
    (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).binders.symm
  have sourcePacked : checked.catalog.project
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))) =
      .ok (SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd)) := by
    simpa only [parameters, List.map_map, Function.comp_def] using packed
  have projectedFunction := code.projection
  change (do pure (checked.catalog.functionType
    (← checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))))
    (← checked.catalog.project function.resultType))) = _ at projectedFunction
  rw [sourcePacked, resultProjected] at projectedFunction
  simp only [bind, Except.bind, pure, Except.pure, SourceCoreCompatibleCatalog.Catalog.functionType,
    profile, ↓reduceIte, Except.ok.injEq] at projectedFunction
  exact (callable_parameters projectedFunction).1.symm

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Native tags authenticate only the retained native parameter/result shape. -/
theorem association_native_type
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  cases association with
  | ordinary _ _ _ _ _ _ _ _ _ typed _ _ => exact typed.type_eq
  | principal _ _ _ _ _ _ _ _ _ typed _ _ => exact typed.type_eq

/-- The selected complete static body supplies its true result projection;
the actual binder projection vector remains an independent authentic receipt. -/
theorem association_binding_pack
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    exact code_binding_pack code profile projected support.body.projection
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    exact code_binding_pack code profile projected support.body.projection

section Compiler
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {sourceType : TypeSystem.Ty}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}

/-- The actual successful callee payload and genuine callable policy fix the
compiler's two native types at exactly the selected complete association. -/
theorem compiler_parameters
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type) :
    receipt.parameterType = parameterCore ∧ receipt.resultType = resultCore := by
  have actualType := represented.runtime_hasType.type_eq
  have selectedType := association_native_type association
  have accepted := receipt.callableType
  rw [actualFunctionType] at accepted
  exact callable_parameters (accepted.trans (actualType.symm.trans selectedType))

/-- The existing packing type theorem retains the actual compiler vector. -/
theorem compiler_parameter_pack
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) = parameterCore :=
  (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
    (receipt.packedType.symm.trans (compiler_parameters receipt actualFunctionType association represented).1)

/-- Genuine selected binder projections close the native pack equality;
raw Source bundle equality and actual arity are not replaced by this result. -/
theorem compiler_binding_pack
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (association : CallableIndexedOwnedStoredClosureInvocation.Association
      headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world
      sourceType (.closure function) native receipt.calleeCode.type)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (projected : ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
  (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (association_binding_pack association profile projected)

end Compiler
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
