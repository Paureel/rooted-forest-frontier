import HardPaidSourceBound
example : (([1,2,2,5]:List Nat).map (fun d=>if d≤3 then 2^(3-d) else 0)).sum=6 := by decide +kernel
