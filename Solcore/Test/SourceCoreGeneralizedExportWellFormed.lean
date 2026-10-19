import Solcore.Test.SourceCoreGeneralizedExportTyping

/-! Every original function receives its own declarative body proof. The
ordered list is the complete checked program, including the intervening tick. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics

structure FunctionTyping (signatures : ProgramSignatures) (function : CheckedFunction) where
  signature : ProgramFunctionSignature
  member : signature ∈ signatures.functions
  owner : function.declaration = signature.id
  body : BodyTyping signatures function signature

inductive FunctionTypings (signatures : ProgramSignatures) : List CheckedFunction → Type where
  | nil : FunctionTypings signatures []
  | cons {function rest} (head : FunctionTyping signatures function)
      (tail : FunctionTypings signatures rest) : FunctionTypings signatures (function :: rest)

theorem FunctionTypings.at {signatures : ProgramSignatures} {functions : List CheckedFunction}
    (rows : FunctionTypings signatures functions) {function : CheckedFunction}
    (member : function ∈ functions) : Nonempty (FunctionTyping signatures function) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ ⟨head⟩
    · exact ih member

structure OriginalTyping (fixture : CompiledFixture) where
  functions : FunctionTypings fixture.recipe.compiled.sourceProgram.signatures fixture.recipe.compiled.sourceProgram.functions
  methods : fixture.recipe.compiled.sourceProgram.methods = []

theorem OriginalTyping.wellFormed {fixture : CompiledFixture} (original : OriginalTyping fixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  apply programWellFormed_ofCheckProgram_statements fixture.checked
  constructor
  · intro function member signature signatureMember accepted
    obtain ⟨typed⟩ := original.functions.at member
    have signatureEq : signature = typed.signature := by
      apply eq_of_mem_of_nodup_map (SignatureCatalogWellFormed.ofCheckProgram fixture.checked).function_ids
        signatureMember typed.member
      exact (checkFunctionBody_success_declaration accepted).symm.trans typed.owner
    subst signature
    exact typed.body.statements_typed
  · intro method member
    rw [original.methods] at member
    cases member

def observeFunctions (signatures : ProgramSignatures) : (functions : List CheckedFunction) →
    IO (FunctionTypings signatures functions)
  | [] => pure .nil
  | function :: rest => do
    match found : signatures.functions.find? (fun signature => decide (signature.id = function.declaration)) with
    | none => throw (IO.userError "export original signature membership")
    | some signature =>
      let body ← observeBodyTyping signatures function signature
      let tail ← observeFunctions signatures rest
      return .cons {
        signature := signature
        member := List.mem_of_find?_eq_some found
        owner := (of_decide_eq_true (List.find?_some
          (p := fun signature : ProgramFunctionSignature => decide (signature.id = function.declaration)) found)).symm
        body := body } tail

def observeOriginalTyping (fixture : CompiledFixture) : IO (OriginalTyping fixture) := do
  let functions ← observeFunctions fixture.recipe.compiled.sourceProgram.signatures fixture.recipe.compiled.sourceProgram.functions
  let ⟨count⟩ ← observed (fixture.recipe.compiled.sourceProgram.methods.length = 0) "export complete original method list"
  return ⟨functions,List.length_eq_zero_iff.mp count⟩

def typingProbe : IO Unit := do
  let fixture ← compileProfiledFixture
  let original ← observeOriginalTyping fixture.original
  let _wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram) := original.wellFormed
  IO.println "GENERALIZED_EXPORT_ORIGINAL_TYPING: originals3/cache3/profile3/typed3"
  IO.println "GENERALIZED_EXPORT_DECLARATIVE_TYPING_PASS"

end Tests.SourceCoreGeneralizedExport
