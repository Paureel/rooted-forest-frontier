import Lean
import FinalWork
open Lean RMAF Universal233.CoreProgram Universal233.FinalCutRecovery Universal233.SourceCoverage
def main : IO Unit := do
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "0/2"),("mass",toJson (toString (rawQMass 2 (generate (.leaf 0) (blockColor [[0]]) 0).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "0/233/100"),("mass",toJson (toString (rawQMass (mkRat 233 100) (generate (.leaf 0) (blockColor [[0]]) 0).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "0/3"),("mass",toJson (toString (rawQMass 3 (generate (.leaf 0) (blockColor [[0]]) 0).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "1/2"),("mass",toJson (toString (rawQMass 2 (generate (.node (.leaf 0) (.leaf 1)) (blockColor [[0],[1]]) 1).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "1/233/100"),("mass",toJson (toString (rawQMass (mkRat 233 100) (generate (.node (.leaf 0) (.leaf 1)) (blockColor [[0],[1]]) 1).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "1/3"),("mass",toJson (toString (rawQMass 3 (generate (.node (.leaf 0) (.leaf 1)) (blockColor [[0],[1]]) 1).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "2/2"),("mass",toJson (toString (rawQMass 2 (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0,1],[2],[3]]) 2).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "2/233/100"),("mass",toJson (toString (rawQMass (mkRat 233 100) (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0,1],[2],[3]]) 2).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "2/3"),("mass",toJson (toString (rawQMass 3 (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0,1],[2],[3]]) 2).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "3/2"),("mass",toJson (toString (rawQMass 2 (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0],[1],[2],[3]]) 3).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "3/233/100"),("mass",toJson (toString (rawQMass (mkRat 233 100) (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0],[1],[2],[3]]) 3).outputs)))]).compress)
 IO.println ("RAW_MASS " ++ (Json.mkObj [("id",toJson "3/3"),("mass",toJson (toString (rawQMass 3 (generate (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (blockColor [[0],[1],[2],[3]]) 3).outputs)))]).compress)
