/*
1. Soundness
2. Completeness
3. Termination
	- Use the variant max_h - d where max_h is the maximum element of list s.
	- The wellfounded relation is proved by:
		(max_h - d) - (max_h - (d+1)) > 0
		(max_h - d) >= 0
4. Harness
*/