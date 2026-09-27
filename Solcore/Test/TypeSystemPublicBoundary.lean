import Solcore.TypeSystem

set_option autoImplicit false

namespace Tests

example := @Solcore.TypeSystem.InferState.fresh_substitution
example := @Solcore.TypeSystem.InferState.fresh_next
example := @Solcore.TypeSystem.InferState.instantiate_substitution
example := @Solcore.TypeSystem.InferState.instantiateDeclaration_substitution
example := @Solcore.TypeSystem.InferState.unify_next
example := @Solcore.TypeSystem.InferState.solve_next

end Tests
