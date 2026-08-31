import Solcore.Syntax.Parser.TriviaProperties

/-! External consumers for canonical comment-attachment validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @commentsDirectlyBefore_validFor
example := @TriviaInternals.attachTraitMethodComments_validFor
example := @TriviaInternals.attachTraitComments_validFor
example := @TriviaInternals.attachImplMethodComments_validFor
example := @TriviaInternals.attachImplComments_validFor
example := @attachTopItemComments_leading_validFor
example := @attachTopItemComments_trait_validFor
example := @attachTopItemComments_impl_validFor

end Tests
