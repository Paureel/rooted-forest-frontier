import PureBridge
open PureBridge
-- Deliberately false: omit the deepest-root depth condition.
example : ([false] : Address).IsPrefix [] := by decide
