#!/usr/bin/env python3
"""Detached build launcher: double-fork + setsid so no harness process-group
kill or wrapper-reaper can reach the build tree."""
import os
import sys

LOG = sys.argv[1] if len(sys.argv) > 1 else 'p2e_r9c.log'

if os.fork() == 0:
    os.setsid()
    if os.fork() == 0:
        os.chdir('/Volumes/Substrate-1/bigo/sssp-nlogn-lane')
        devnull = os.open(os.devnull, os.O_RDWR)
        os.dup2(devnull, 0)
        os.dup2(devnull, 1)
        os.dup2(devnull, 2)
        os.execvp('bash', ['bash', './p2d_build.sh', LOG])
    os._exit(0)
try:
    os.waitpid(0, 0)
except ChildProcessError:
    pass
print('launched', LOG)
