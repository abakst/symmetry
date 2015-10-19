import sys
import os
import subprocess
import glob

failed = []
posDir = "tests/pos"
negDir = "tests/neg"

def runTestsInDir(dir, expect):
    failed = []
    for i in glob.glob(os.path.join(dir,"*.hs")):
        sys.stdout.write ("[%s]: " % i)
        return_code = subprocess.call(["runghc", i,"--verify"])
        if return_code == expect:
            print "\033[1;32mPASS\033[0;0m"
        else:
            print "\033[1;31mFAIL\033[0;0m"
            failed += i
            print ""
    return failed

failed += runTestsInDir(posDir, 0)
failed += runTestsInDir(negDir, 1)

if failed == []:    
    print "All tests passed!"
    exit(0)
else:
    print "Failed Tests:"    
    for t in failed:
        print t
    exit(1)
