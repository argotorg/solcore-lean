import Solcore.Syntax.Parser.Trivia

/-! External consumers for canonical comment-attachment validity. -/

namespace Tests

open Solcore.Syntax.Parser

example := @commentsDirectlyBefore_validFor
example := @TriviaInternals.attachEnumConstructorComments_mem
example := @TriviaInternals.attachEnumConstructorComments_validFor
example := @TriviaInternals.attachEnumConstructors_validFor
example := @TriviaInternals.attachEnumComments_validFor
example := @TriviaInternals.attachTraitMethodComments_validFor
example := @TriviaInternals.attachTraitComments_validFor
example := @TriviaInternals.attachImplMethodComments_validFor
example := @TriviaInternals.attachImplComments_validFor
example := @TriviaInternals.attachContractMemberComments_validFor
example := @TriviaInternals.attachContractComments_validFor
example := @attachTopItemComments_leading_validFor
example := @attachTopItemComments_trait_validFor
example := @attachTopItemComments_impl_validFor
example := @attachTopItemComments_validFor
example := @attachTopItemComments_span
example := @attachTopItemComments_list_validFor
example := @parsedFile_withAttachedComments_validFor

end Tests
