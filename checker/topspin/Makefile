EXE       = sympan
GCC       = gcc
CFLAGS    = -O2 -DVECTORSZ=4096 -DSAFETY -DNOBOUNDCHECK -DNOCOMP -DSFH -DNOFAIR
MY_HEADER = topspin_header_fix.c

.PHONY: all clean

all: $(EXE)

out2.pml: out.pml FORCE
	spin -D__K__=$(K) -I $< | sed 's/proctype :init:()/init/g' > $@

$(EXE): sympan_fix.c FORCE
	$(GCC) -o $@ $(CFLAGS) $< group.c

sympan.c: out2.pml
	java -jar $(JAR) $<

sympan_fix.c: sympan.c config.txt FORCE
	(cat $(MY_HEADER) ; cat $<) > $@

pan: pan.c FORCE
	$(GCC) -o $@ $(CFLAGS) $<

pan.c: loadbalancer.p FORCE
	spin -a loadbalancer.p

clean:
	rm -rf $(EXE) pan* sympan* group.* groupinfo \
		apply_permutation.h symmetry_group.h

FORCE:
