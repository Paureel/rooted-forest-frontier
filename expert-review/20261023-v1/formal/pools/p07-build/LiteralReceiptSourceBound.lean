import LiteralScheduleReceiptSource
namespace OrdinaryDispatch.Hard2SourceWork
open Universal233 WholeSourceWork PaidQueries

theorem literalScheduleSource_queries {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) :
 (literalScheduleSource f q js).value.queries=(scheduleSourceMeter f q js).queries:=by
 rw [literalScheduleSource_value,scheduleSourceMeter_queries]

theorem literalScheduleSource_local_bound {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) :
 (literalScheduleSource f q js).localWork≤128*(js.length+1):=by
 rw [(literalScheduleSource_work f q js).1]
 exact scheduleSourceMeter_caller_bound f q js

theorem literalScheduleSource_callback_split {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) :
 (literalScheduleSource f q js).callbackWork=
  ((literalScheduleSource f q js).value.queries.map (fun pb=>(f pb.1 pb.2).work)).sum:=by
 rw [(literalScheduleSource_work f q js).2,literalScheduleSource_queries]
 exact scheduleSourceMeter_callback_split f q js

theorem literalScheduleSource_query_origin {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
 (q : Nat) (js : List (Job P A)) (pb : P×Nat) (h:pb∈(literalScheduleSource f q js).value.queries) :
 .hard pb.1∈js ∧ pb.2=allocated q js:=by
 rw [literalScheduleSource_queries] at h
 exact scheduleSourceMeter_query_origin f q js pb h
end OrdinaryDispatch.Hard2SourceWork
