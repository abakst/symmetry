#!/usr/bin/env python

import sys
import os
import subprocess
import glob
import getpass

savedPath = os.getcwd()

def get_config():
    d = {}
    project_dir = os.path.dirname(os.path.realpath(__file__))
    isStack = os.path.isfile(os.path.join(project_dir, "stack.yaml"))
    if isStack:
        runghc = ["stack", "runghc", "--"]
    else:
        runghc = ["runghc"]
    return { "runghc"      : runghc
           , "project_dir" : project_dir
           , "isStack"     : isStack
           }

config = get_config()
os.chdir(config["project_dir"])

failed = []
posDir = "tests/pos"
negDir = "tests/neg"

def runTestsInDir(dir, expect):
    failed = []
    for i in glob.glob(os.path.join(dir, "*.hs")):
        sys.stdout.write ("[%s]: " % i)
        return_code = subprocess.call(config["runghc"] + [i,"--verify"])
        if return_code == expect:
            print "\033[1;32mPASS\033[0;0m"
        else:
            print "\033[1;31mFAIL\033[0;0m"
            failed.append(i)
            print ""
    return failed

def install_lib():
    if config["isStack"]:
        rc = subprocess.call(["stack", "clean"])
        if rc != 0:
            print "\033[1;31mERROR: 'stack clean' failed\033[0;0m"
            sys.exit(1)
        rc = subprocess.call(["stack", "install"])
        if rc != 0:
            print "\033[1;31mERROR: 'stack install' failed\033[0;0m"
            sys.exit(1)

install_lib()

failed += runTestsInDir(posDir, 0)
failed += runTestsInDir(negDir, 1)

os.chdir(savedPath)

if failed == []:
    print "All tests passed!"
    exit(0)
else:
    print "Failed Tests:"
    for t in failed:
        print t
    exit(1)
