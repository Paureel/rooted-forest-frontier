import Rule4OccurrenceV3

namespace SourceRule4V3

def toRecorded (cells : List Cell) (x : {ls // ls∈chronological cells}) :
    {ls // ls∈recorded cells} := ⟨x.val,(two_ledger_perm cells).mem_iff.mp x.property⟩

def toChronological (cells : List Cell) (x : {ls // ls∈recorded cells}) :
    {ls // ls∈chronological cells} := ⟨x.val,(two_ledger_perm cells).mem_iff.mpr x.property⟩

theorem occurrence_left_inverse (cells : List Cell) (x : {ls // ls∈chronological cells}) :
    toChronological cells (toRecorded cells x)=x := rfl

theorem occurrence_right_inverse (cells : List Cell) (x : {ls // ls∈recorded cells}) :
    toRecorded cells (toChronological cells x)=x := rfl

theorem occurrence_preserves_every_slot_field (cells : List Cell)
    (x : {ls // ls∈chronological cells}) :
    (toRecorded cells x).val.1=x.val.1 ∧
    (toRecorded cells x).val.2=x.val.2 := ⟨rfl,rfl⟩

end SourceRule4V3
