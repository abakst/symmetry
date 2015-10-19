import os
import subprocess
import glob

failed = []

for i in glob.glob("tests/pos/*.hs"):
    print "[%s]" % i
    return_code = subprocess.call(["runghc", i,"--verify"])
    if return_code == 0:
        print "PASS"
    else:
        print "FAIL"
        failed += i
    print ""

for i in os.listdir("tests/neg"):
    print "[%s]" % i
    return_code = subprocess.call(["runghc", i,"--verify"])
    if return_code == 0:
        print "FAIL"
        failed += i
    else:
        print "PASS"
    print ""

if failed == []:    
    print "All tests passed!"
    exit(0)
else:
    print "Failed Tests"    
    for t in failed:
        print t
    exit(1)
