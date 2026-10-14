import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodNodeFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission

/-! The closed coercion lane retains flat checks for every actual cached
method and the existing complete selected coercion catalog. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompilerCoercedMethodProfile
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (metadata?)
open CallableIndexedOwnedPreparedPrimitiveMethodAdmission (Excluded)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)
open SelectedCompilationAcceptedPrimitiveMethods (Forms forms?)

structure Primitive (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) where
  noOrdinary : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
    named.specialized.declaration ≠ signature.id
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution
  expression : ExpressionId
  terminal : Terminal named.specialized.function.typedBody expression
    (statements named.specialized.function.typedBody)
  forms : Forms named.specialized.function.typedBody
  formsAccepted : ∃ receipt, forms? named.specialized.function.typedBody = some receipt
  metadataAccepted : ∃ receipt,
    metadata? compiled.indexed named named.specialized.function.typedBody (fun _ => False) = some receipt

def primitive? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Option (Primitive compiled named) := do
  if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
      decide (named.specialized.declaration ≠ signature.id)) = true then
   let ⟨range⟩ ← CallableIndexedOwnedPreparedOrdinarySyntaxTable.range?
     compiled.sourceProgram.signatures (max 1 compiled.indexed.fuel) named.specialized.parameterSubstitution
   let source := named.specialized.function.typedBody
   match formsAccepted : forms? source with
   | none => none
   | some ⟨forms⟩ =>
     match metadataAccepted : metadata? compiled.indexed named source (fun _ => False) with
     | none => none
     | some receipt =>
       match roots : statements source with
       | [] => none
       | first :: rest =>
         match found : source.lookupStatement? first with
         | none => none
         | some node =>
           match form : node.form with
           | .returnStmt (some expression) =>
             pure ⟨(fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member)),
               range, expression, by rw [roots]; exact .returning rest found form,
               forms, ⟨⟨forms⟩, formsAccepted⟩, ⟨receipt, metadataAccepted⟩⟩
           | _ => none
  else none

structure Closed (compiled : SourceCoreUnifiedCompilation.Compiled) : Type where
  catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled
  methods : ∀ named ∈ compiled.indexed.base.functions,
    Excluded compiled named ∨ Nonempty (Primitive compiled named)

private def methods? (compiled : SourceCoreUnifiedCompilation.Compiled) :
    (rows : List SourceCoreGeneralFunctions.Function) →
      Option (PLift (∀ named ∈ rows, Excluded compiled named ∨ Nonempty (Primitive compiled named)))
  | [] => some ⟨by intro named member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
        (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      some ⟨Or.inl (by
        intro definition member
        exact of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
      else do
        let profile ← primitive? compiled first
        pure ⟨Or.inr ⟨profile⟩⟩ : Option (PLift (Excluded compiled first ∨ Nonempty (Primitive compiled first))))
    let ⟨tail⟩ ← methods? compiled rest
    pure ⟨by
      intro named member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail named member⟩

def certify (compiled : SourceCoreUnifiedCompilation.Compiled) : Option (Closed compiled) := do
  let ⟨catalog⟩ ← CallableIndexedOwnedPreparedClosedCoercionAdmission.certify compiled
  let ⟨methods⟩ ← methods? compiled compiled.indexed.base.functions
  pure ⟨catalog, methods⟩

end Solcore.SourceSemantics.CoreLowering.CompilerCoercedMethodProfile
