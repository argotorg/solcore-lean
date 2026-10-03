import Solcore.SourceSemantics.Instantiation
import Solcore.Frontend.SourceCoreDataCatalog

/-! Closed retained types recover source validity in the real residual scope.
Every substitution row, including unused parameters, is checked. These lemmas
never change a source context's residual flag. The actual compiler must supply
the closedness receipts separately; native type tags cannot supply them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
open Frontend SourceInference

theorem no_free_variables (type : TypeSystem.Ty)
    (closed : SourceCoreDataCatalog.closed type = true) : type.freeVariables = [] := by
  induction type with
  | «variable» | «parameter» | error => simp [SourceCoreDataCatalog.closed] at closed
  | constructor => rfl
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
    simp only [SourceCoreDataCatalog.closed, Bool.and_eq_true] at closed
    simp only [TypeSystem.Ty.freeVariables, leftIH closed.1, rightIH closed.2]
    rfl
  | proxy inner ih | comptime inner ih => exact ih closed

theorem well_formed {context : Context} {type : TypeSystem.Ty}
    (admissible : TypeAdmissible context type) (lexical : context.typeVariables = [])
    (closed : SourceCoreDataCatalog.closed type = true) : TypeWellFormed context type := by
  refine ⟨admissible.binders, ?_⟩
  simpa [admissibleTypeVariables, lexical, no_free_variables type closed] using admissible.typeWellScoped

def ClosedParameterRange (substitution : TypeSystem.ParameterSubstitution) : Prop :=
  ∀ parameter replacement, (parameter, replacement) ∈ substitution →
    SourceCoreDataCatalog.closed replacement = true

theorem range_well_formed {context : Context} {substitution : TypeSystem.ParameterSubstitution}
    (admissible : ParameterSubstitution.RangeAdmissible context substitution)
    (lexical : context.typeVariables = []) (closed : ClosedParameterRange substitution) :
    ParameterSubstitution.RangeWellFormed context substitution := by
  intro parameter replacement member
  exact well_formed (admissible parameter replacement member) lexical (closed parameter replacement member)

theorem declaration_valid {context : Context} {instantiation : DeclarationInstantiation}
    (admissible : DeclarationInstantiation.Admissible context instantiation)
    (lexical : context.typeVariables = [])
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    DeclarationInstantiation.Valid context instantiation := by
  cases admissible with
  | intro signature member declaration domain range type predicates parameterComptime returnComptime =>
    exact .intro signature member declaration domain (range_well_formed range lexical closed)
      type predicates parameterComptime returnComptime

theorem constructor_valid {context : Context} {instantiation : DataConstructorInstantiation}
    (admissible : DataConstructorInstantiation.Admissible context instantiation)
    (lexical : context.typeVariables = [])
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    DataConstructorInstantiation.Valid context instantiation := by
  cases admissible with
  | intro data signature member signatureMember owner constructor domain range payload result =>
    exact .intro data signature member signatureMember owner constructor domain
      (range_well_formed range lexical closed) payload result

end Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
