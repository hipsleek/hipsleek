/*
Solution:
1. Safety
2. Termination
	- Use the lexicographical order [j, length(a) - i] to prove the termination
	in 3 cases:
		+ (i, j) -> (i+1, j): [j, length(a) - i] > [j, length(a) - (i+1)]
		+ (i, j) -> (i, j-1): [j, _] > [j-1, _]
		+ (i, j) -> (i+1, j-1): [j, _] > [j-1, _]
3. Behavior
*/