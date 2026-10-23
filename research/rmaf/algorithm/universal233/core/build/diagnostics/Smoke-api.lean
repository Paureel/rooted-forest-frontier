import Std
example : (2 : Nat) + 2 = 4 := by decide
#check List.append_cancel_left
#check List.append_cancel_right
#check List.dropLast_append_cons
#check List.dropLast_concat
#check List.dropLast_append
#check List.append_inj
#check List.append_inj_left
#check List.isPrefix_iff
#check List.IsPrefix.eq_of_length_le
#check List.IsPrefix.eq_of_length
#check List.append_injective_left
#check List.append_injective_right
