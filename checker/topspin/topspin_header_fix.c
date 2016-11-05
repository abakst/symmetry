#if VECTORSZ>32000
	extern int 
#else
	extern short 
#endif
	*proc_offset, *q_offset;

unsigned long int vsize;	/* vector size in bytes */
