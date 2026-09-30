import Solcore.SourceSemantics.CoreLowering.FunctionArguments

/-! Parameter allocation over a heap with administrative closure values.
The continuation creates a fresh closure under the actual temporary-binder
layout. No assumption equates that capture with the canonical environment. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionArguments
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Core GeneralHeap FunctionArguments

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"function_arguments", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "parameter", scheme := .mono type }
private def bindings : List (TypedBinder × Ty) := [(binder 0 .word, .word), (binder 1 .bool, .bool)]
private def sources : List Dynamic.Value := [.word Word.zero, .bool true]
private def values : List Value := [.word Word.zero, .bool true]
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def model : GenericHeap.PayloadModel catalog := GenericHeap.finitePayload catalog signatures
private def functionType : Ty := .function .unit .unit
private def administrative : Value := .closure .unit .unit (.var 0) []
private def world : StoreTyping := [functionType]
private def store : Store := [administrative]
private def canonical : Environment := [administrative]
private def actual : Environment := [DataPatternValues.packValues values, .integer 9, administrative]
private def embedding : Renaming := Renaming.insertion 1
private def body : Expr := LanguageResult.success (.lambda .unit .unit .unit)

private theorem represented : Arguments model [] world bindings sources values :=
  .cons ⟨rfl, .word _⟩ (.cons ⟨rfl, .bool _⟩ .nil)

private theorem heaps : GenericHeap.HeapRepresents model [] world ⟨[]⟩ store :=
  GenericHeap.HeapRepresents.empty.allocate_administrative (.closure .nil (.var rfl))

private theorem environments : DataHeap.EnvRepresents catalog [] world [functionType] [] [] canonical :=
  .nil (.cons (.closure .nil (.var rfl)) .nil)

private theorem actualLayout : ReadOnly.EnvironmentsAgree embedding
    (DataPatternValues.packValues values :: canonical) actual :=
  ReadOnly.EnvironmentsAgree.insertion (DataPatternValues.packValues values :: canonical) 1 (.integer 9)

/-- Both source arguments are allocated, then the arbitrary continuation may
capture its real Core environment. Removing the prefix recovers exactly the
same continuation evaluation and store, even for that newly created closure. -/
example : ∃ sourceEnvironment heap finalCanonical captured finalStore mapping finalWorld finalEmbedding,
    Dynamic.BindersAllocate [] ⟨[]⟩ (bindings.map Prod.fst) sources sourceEnvironment heap ∧
    DataHeap.EnvRepresents catalog mapping finalWorld [functionType]
      (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) [])
      sourceEnvironment finalCanonical ∧
    GenericHeap.HeapRepresents model mapping finalWorld heap finalStore ∧
    AdministrativePreserved [] store mapping finalStore ∧
    ReadOnly.EnvironmentsAgree finalEmbedding finalCanonical captured ∧
    Evaluates actual store
      ((SourceCoreFunctions.bindParameters bindings functionType (body.weakenAt bindings.length)).rename embedding)
      (.inRight .word (.closure .unit .unit .unit captured)) finalStore ∧
    (∀ result future,
      Evaluates actual store
        ((SourceCoreFunctions.bindParameters bindings functionType (body.weakenAt bindings.length)).rename embedding)
        result future → Evaluates captured finalStore (body.rename finalEmbedding) result future) := by
  obtain ⟨sourceEnvironment, heap, finalCanonical, captured, finalStore, mapping, finalWorld, finalEmbedding,
    allocated, environments, heaps, _, _, frame, layout, agreement⟩ :=
    parameters_prefix represented (body := body) (outputType := functionType) environments heaps actualLayout
  refine ⟨sourceEnvironment, heap, finalCanonical, captured, finalStore, mapping, finalWorld, finalEmbedding,
    allocated, environments, heaps, frame, layout, agreement.wrap ?_, ?_⟩
  · exact .inRight .lambda
  · intro result future evaluation
    exact agreement.unwrap evaluation

end Tests.SourceCoreFunctionArguments
