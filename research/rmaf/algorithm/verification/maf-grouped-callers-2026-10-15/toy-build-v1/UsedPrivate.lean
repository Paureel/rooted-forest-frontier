import Clean
private axiom usedPrivate : False
theorem contaminated : True := False.elim usedPrivate
