.PHONY: check verify-manifest verify-small verify-formal setup toolkit

check: verify-manifest verify-small

verify-manifest:
	./bootloops-python scripts/check_repository.py

verify-small:
	./bootloops-python scripts/verify_small_instances.py

verify-formal:
	./bootloops-python scripts/verify_small_instances.py --formal-only

setup:
	python3 -m venv .venv
	.venv/bin/python -m pip install -r requirements.txt

toolkit:
	./bootloops-python scripts/bootstrap_toolkit.py
