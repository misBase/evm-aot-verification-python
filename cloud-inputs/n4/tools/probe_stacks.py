"""cloud-inputs/n2/tools/probe_traced.py plus a dump of every thread's Python stack every
STACKS_EVERY seconds (default 600) to STACKS_FILE (faulthandler), so a node that stops logging
shows where it is. Diagnostics only; arguments as probe_traced.py.
"""
import faulthandler
import os
import runpy
import sys

every = float(os.environ.get("STACKS_EVERY", "600"))
stacks = open(os.environ.get("STACKS_FILE", "stacks.txt"), "w")
faulthandler.dump_traceback_later(every, repeat=True, file=stacks)
sys.argv = ["probe_traced.py", *sys.argv[1:]]
runpy.run_path("cloud-inputs/n2/tools/probe_traced.py", run_name="__main__")
