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
 * ed(s[0..n],t[0..m]) = m + n if either n or m is 0 i.e. one of s, t is empty
 *                     = ed(s[0..n-1],t[0..m-1])
 *                          if s[n] = t[m]
 *                     = 1 + min{ed(s[0..n-1],t[0..m-1]),  substitute s[m] --> t[n] & then transform s[0..n-1] --> t[0..m-1]
                                 ed(s[0..n-1],t[0..m]),    delete s[n] & transform s[0..n-1] --> t[0..m]
                                 ed(s[0..n],t[0..m-1])     insert t[m] & transform s[0..n] --> t[0..m-1] }
 *                          otherwise
 *         
 * In the restricted version, the formula is fairly similar
 * 
 * ed(s[0..n],t[0..m]) = max(m,n,0)            if either n or m is < 0 i.e. one of s, t is empty
                       = ed(s[0..n-1],t[0..m-1])                                  if s[n] = t[m]
 *                     = 1 + min{ed(s[0..n-1],t[0..m]), ed(s[0..n],t[0..m-1])     otherwise
 *         
 * Reference: Edition distance
 * http://proval.lri.fr/gallery/distance.en.html
 * 
 * @author Vu An Hoa
 */
 
// the content of a[i..j] is identical to b[u..v]
relation identical(int[] a, int i, int j, int[] b, int u, int v) ==
	i - j = v - u & forall(k : k < i | k > j | a[k] = b[u + k - i]).

// d is a distance between two words
relation dist(int[] w1, int l1, int[] w2, int l2, int d).

relation min_dist(int[] w1, int l1, int[] w2, int l2, int d) ==
	dist(w1,l1,w2,l2,d) & forall(m : !(dist(w1,l1,w2,l2,m)) | d <= m).
	
// DEFINING AXIOMS
	
// base case {d = 0} : w1 and w2 are identical
axiom l1 = l2 & identical(w1,1,l1,w2,1,l2) ==> dist(w1,l1,w2,l2,0).

// base case {d = 1} : w2 is obtained by either inserting/deleting an element of w1
axiom l1 = l2 + 1 & 1 <= i <= l1 & identical(w1,1,i-1,w2,1,i-1) 
			& identical(w1,i+1,l1,w2,i,l2) ==> dist(w1,l1,w2,l2,1).
axiom l2 = l1 + 1 & 1 <= i <= l2 & identical(w1,1,i-1,w2,1,i-1) 
			& identical(w1,i,l1,w2,i+1,l2) ==> dist(w1,l1,w2,l2,1).

// induction : (transitivity/additivity) if one can edit w1 --> w2 and w2 --> w3 in
// d and e steps then one can edit w1 --> w3 in d + e steps
axiom dist(w1,l1,w2,l2,d) & dist(w2,l2,w3,l3,e) ==> dist(w1,l1,w3,l3,d+e).

// THEOREMS AND CONSEQUENCES

// (optional theorem) symmetry due to symmetry between insert/delete; proof by induction on d
axiom dist(w1,l1,w2,l2,d) ==> dist(w2,l2,w1,l1,d).
axiom dist(w1,l1,w2,l2,d) ==> dist(w1,l1,w2,l2+1,d+1).
axiom dist(w1,l1,w2,l2,d) ==> dist(w1,l1+1,w2,l2,d+1).
axiom dist(w1,l1,w2,l2,d) & w1[l1+1] = w2[l2+1] ==> dist(w1,l1+1,w2,l2+1,d).
// one of the word is empty
axiom true ==> dist(w1,0,w2,l2,l2).
axiom true ==> dist(w1,l1,w2,0,l1).

// Theorem : Number of edits must be at least the difference in the lengths.
// Why ? Because each edit adjusts the length of the source by 1 and hence, it 
// requires at least |l1-l2| edits to transform a string of length l1 to a
// string of length l2
axiom dist(w1,l1,w2,l2,d) ==> d >= l1 - l2 & d >= l2 - l1.

// Consequences of the above theorem:
//axiom true ==> min_dist(w1,0,w2,l2,l2).
//axiom true ==> min_dist(w1,l1,w2,0,l1).

// Compute smallest number of edits to transform s[1..n] to t[1..m] recursively
int edrec(int[] s, int n, int[] t, int m)
	variance (0) [m + n]
	requires dom(s,1,n) & dom(t,1,m) & n >= 0 & m >= 0
	ensures dist(s, n, t, m, res);
	//ensures min_dist(s, n, t, m, res);
{
	// either s or t is empty ==> delete entire or insert entire t to s to get t
	if (n == 0 || m == 0)
		return m + n;
	// otherwise: both s and t are not empty m, n > 0
	else if (s[n] == t[m])
		return edrec(s,n-1,t,m-1);
	else {
		int d1 = 1 + edrec(s,n-1,t,m);
		int d2 = 1 + edrec(s,n,t,m-1);
		if (d1 < d2)
			return d1;
		else
			return d2;
	}
}

/*
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
*/

