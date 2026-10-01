import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.ProgramInterfaces
import Solcore.Abi.StaticWord

/-! Entry and Static Word root discovery, independent of runtime selection.
All roots subsequently enter the same cached Core compiler and ownership
session. Loading and checking the conventional entry happens once. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreRootDiscovery
open TypeSystem
abbrev Seed := SourceCoreCompiler.Seed

structure CheckedEntry (raw : Workspace.RawWorkspace) (fuel : Nat) where private mk ::
  program : CheckedProgram
  moduleId : Workspace.ModuleId
  private checked : checkProgram raw fuel = .ok program

theorem CheckedEntry.source_checked {raw : Workspace.RawWorkspace} {fuel : Nat}
    (entry : CheckedEntry raw fuel) : checkProgram raw fuel = .ok entry.program := entry.checked

def checkEntry (raw : Workspace.RawWorkspace) (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (CheckedEntry raw fuel) :=
  match loaded : loadProgram raw with
  | .error errors => .error (errors.map ProgramCheckError.loading)
  | .ok loadedProgram =>
      match checked : checkLoadedProgram loadedProgram fuel with
      | .error errors => .error errors
      | .ok program => .ok ⟨program, loadedProgram.workspace.entry.toModuleId, by
          simp only [checkProgram, loaded, checked]⟩

def CheckedEntry.seed {raw : Workspace.RawWorkspace} {fuel : Nat} (entry : CheckedEntry raw fuel) : Seed :=
  SourceCoreCompiler.Seed.named entry.moduleId "main"

structure StaticWordRoot where
  metadata : Abi.V1.MethodMetadata
  seed : Seed

/-- Exact discovery failures for the exported Static Word source profile. -/
inductive StaticWordRootError where
  | interfaces (errors : List ProgramInterfaceError)
  | unknownEntryModule (moduleId : Workspace.ModuleId)
  | invalidMethodName (name : String)
  | missingSignature (declaration : Resolved.DeclarationId)
  | duplicateSignatures
      (declaration : Resolved.DeclarationId) (count : Nat)
  | genericFunction
      (declaration : Resolved.DeclarationId) (name : String) (arity : Nat)
  | unsupportedParameters
      (declaration : Resolved.DeclarationId) (name : String)
      (types : List Ty) (comptime : List Bool)
  | unsupportedResults
      (declaration : Resolved.DeclarationId) (name : String)
      (types : List Ty) (comptime : Bool)
  | duplicateSignature
      (firstName secondName : String) (signature : String)
  | selectorCollision
      (firstName secondName : String)
      (firstSignature secondSignature : String)
      (selector : Abi.V1.Selector)
  | noRoots (moduleId : Workspace.ModuleId)
  deriving Repr

private def staticWordRootOfEntity (program : CheckedProgram)
    (entity : ProgramPublicEntity) : Except StaticWordRootError StaticWordRoot := do
  let methodName ← match Abi.V1.validateMethodName? entity.publicName with
    | some name => pure name
    | none => throw (.invalidMethodName entity.publicName)
  let candidates := program.signatures.functions.filter fun signature =>
    decide (signature.id = entity.declaration.id)
  let signature ← match candidates with
    | [signature] => pure signature
    | [] => throw (.missingSignature entity.declaration.id)
    | signatures =>
        throw (.duplicateSignatures entity.declaration.id signatures.length)
  unless signature.scheme.parameters.isEmpty do
    throw (.genericFunction signature.id entity.publicName
      signature.scheme.parameters.length)
  match signature.parameters with
  | [parameter] =>
      unless parameter.type == .word && !parameter.comptime do
        throw (.unsupportedParameters signature.id entity.publicName
          signature.parameterTypes signature.parameterComptime)
  | _ =>
      throw (.unsupportedParameters signature.id entity.publicName
        signature.parameterTypes signature.parameterComptime)
  unless signature.returnTypes == [.word] && !signature.returnComptime do
    throw (.unsupportedResults signature.id entity.publicName
      signature.returnTypes signature.returnComptime)
  pure {
    metadata := Abi.V1.MethodMetadata.staticWord methodName
    seed := SourceCoreCompiler.Seed.declaration signature.id
  }

private def staticWordRootsOfEntities (program : CheckedProgram) :
    List ProgramPublicEntity → Except StaticWordRootError (List StaticWordRoot)
  | [] => .ok []
  | entity :: rest =>
      if entity.declaration.kind == .function then do
        let root ← staticWordRootOfEntity program entity
        let roots ← staticWordRootsOfEntities program rest
        pure (root :: roots)
      else
        staticWordRootsOfEntities program rest

private structure IndexedStaticWordRoot where
  root : StaticWordRoot
  signature : String
  selector : Abi.V1.Selector

private def indexStaticWordRoot (root : StaticWordRoot) :
    IndexedStaticWordRoot := {
  root
  signature := root.metadata.canonicalSignatureText
  selector := root.metadata.selector
}

private def IndexedStaticWordRoot.signatureLE
    (left right : IndexedStaticWordRoot) : Bool :=
  (compare left.signature right.signature).isLE

private def canonicalStaticWordRoots
    (roots : List StaticWordRoot) : List IndexedStaticWordRoot :=
  (roots.map indexStaticWordRoot).mergeSort IndexedStaticWordRoot.signatureLE

private def firstDuplicateStaticWordSignature? :
    List IndexedStaticWordRoot →
      Option (IndexedStaticWordRoot × IndexedStaticWordRoot)
  | [] => none
  | first :: rest =>
      match rest.find? fun later => later.signature == first.signature with
      | some later => some (first, later)
      | none => firstDuplicateStaticWordSignature? rest

private def firstStaticWordSelectorCollision? :
    List IndexedStaticWordRoot →
      Option (IndexedStaticWordRoot × IndexedStaticWordRoot)
  | [] => none
  | first :: rest =>
      match rest.find? fun later => later.selector == first.selector with
      | some later => some (first, later)
      | none => firstStaticWordSelectorCollision? rest

private def validateStaticWordConflicts (roots : List StaticWordRoot) :
    Except StaticWordRootError Unit :=
  let indexed := canonicalStaticWordRoots roots
  match firstDuplicateStaticWordSignature? indexed with
  | some conflict =>
      .error (.duplicateSignature
        conflict.1.root.metadata.name.text
        conflict.2.root.metadata.name.text conflict.1.signature)
  | none =>
      match firstStaticWordSelectorCollision? indexed with
      | some conflict =>
          .error (.selectorCollision
            conflict.1.root.metadata.name.text
            conflict.2.root.metadata.name.text
            conflict.1.signature conflict.2.signature conflict.1.selector)
      | none => .ok ()

/-- Discover the complete exported Static Word root set of one checked entry
module.  Unsupported exported functions are diagnosed rather than skipped. -/
def discoverStaticWordRoots (program : CheckedProgram)
    (entryModule : Workspace.ModuleId) :
    Except StaticWordRootError (List StaticWordRoot) := do
  let interfaces ← (buildProgramInterfaces program.environment).mapError
    StaticWordRootError.interfaces
  let interface ← match interfaces.interface? entryModule with
    | some interface => pure interface
    | none => throw (.unknownEntryModule entryModule)
  let roots ← staticWordRootsOfEntities program interface.entities
  if roots.isEmpty then
    throw (.noRoots entryModule)
  validateStaticWordConflicts roots
  pure roots


end Solcore.Frontend.SourceCoreRootDiscovery
