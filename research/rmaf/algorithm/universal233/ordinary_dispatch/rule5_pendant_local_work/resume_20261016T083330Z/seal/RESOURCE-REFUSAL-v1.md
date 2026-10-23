# Resource refusal retained

The first ClassifierFalse launch refused before process creation at
`assert shutil.disk_usage(D).free >= 3*1024**3` in pilot_resume.py.
No Lean negative-control execution occurred in that attempt. The measured
free-byte value was not printed by that assertion and is UNKNOWN.
A follow-up read returned `free=18092965888`; disk availability changed between
these checks. The 3GiB rule is unchanged. A bounded retry is permitted only
through the same live-floor runner, retaining the initial refusal here.
