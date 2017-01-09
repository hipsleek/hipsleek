/**
 * Solve the (modified) edit distance problem using Dynamic Programming 
 * technique.
 * Instead of string editing, we deal with array of integers: minimum
 * number of steps to transform a list of integer to another. The original
 * Levenshtein edit distance allows three operations: insert, delete and
 * substitute; the why3 example solved a variant without substitution.
 * 
 * The recurrence relation for Levenshtein edit distance is:
 * 
 * ed(s[0..],t[0..]) = ed(s[1..],t[1..])                            
 *                          if s[0] = t[0]
 *                   = 1 + min{ed(s[1..],t[1..]), ed(s[1..],t), ed(s,t[1..])}
 *                          otherwise
 *         
 * In the restricted version, the formula is
 * 
 * ed(s[0..],t[0..]) = ed(s[1..],t[1..])
 *                          if s[0] = t[0]
 *                   = 1 + min{ed(s[1..],t), ed(s,t[1..])
 *                          otherwise
 *         
 * Reference: Edition distance
 * http://proval.lri.fr/gallery/distance.en.html
 * 
 * @author Vu An Hoa
 */

// d is POSSIBLE distance between w1[i1..j1] and w2[i2..j2]
// <==> there is a sequence of modification w1 --> w2
relation dist(int[] w1, int i1, int j1,
				int[] w2, int i2, int j2, int d) ==
	(i1 > j1 & i2 > j2 & d = 0 | ).
//	| dist_add_left :
//	    forall w1 w2: word, n:int.
//	    dist w1 w2 n -> forall a:a. dist (Cons a w1) w2 (n + 1)
//	| dist_add_right :
//	    forall w1 w2: word, n:int.
//	    dist w1 w2 n -> forall a:a. dist w1 (Cons a w2) (n + 1)
//	| dist_context :
//	    forall w1 w2: word, n:int.
//	    dist w1 w2 n -> forall a:a. dist (Cons a w1) (Cons a w2) n

relation min_dist(int[] w1, int[] w2, int d) ==
	dist(w1,w2,d) & forall(m: (!(dist(w1,w2,m) | d <= m))).

// Compute the edit distance between s and t
int editdist(int[] s, int n1, int[] t, int n2)
//Pre: { length w1 = n1 and length w2 = n2 and length t = n2+1 }
//Post: { min_dist (word_of_array w1) (word_of_array w2) result }
{
	int[] temp = new int[n2 + 1];
	
	// initialization of temp
    for(int i = 0; i <= n2; i++) {
//      invariant { length t = n2+1 and
//                  forall j:int. 0 <= j < i -> t[j] = n2-j }
    	temp[i] = n2 - i;
    }
    
    // loop over w1
    for(int i = n1-1; i >= 0; i--) {
//    	invariant { length t = n2+1 and 
//    	forall j:int. 0 <= j <= n2 -> min_suffix w1 w2 (i+1) j temp[j] }  
    	o = temp[n2];
    	temp[n2] = temp[n2] + 1;
    	// loop over w2
    	for(int j = n2-1; j >= 0; j--) {
//    		invariant { length t = n2+1
//    		and (forall k:int. j < k <= n2 -> min_suffix w1 w2 i k temp[k])
//    		and (forall k:int. 0 <= k <= j -> min_suffix w1 w2 (i+1) k temp[k])
//    		and min_suffix w1 w2 (i+1) (j+1) !o }
    	    u = o;
    	    o = temp[j];
    	    if (w1[i] == w2[j])
    	    	t[j] = u;
    	    else
    	    	t[j] = min(temp[j],temp[j+1]) + 1;
    	}
    }
    return temp[0];
}


