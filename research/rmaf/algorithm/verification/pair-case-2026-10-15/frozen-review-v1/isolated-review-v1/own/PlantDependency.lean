axiom ownUnusedFalse : False
private axiom ownPrivateFalse : False
private theorem ownHiddenFalse : False := ownPrivateFalse
theorem ownExportedFalse : False := ownPrivateFalse
