/**
 * Array sorting using insertion sort.
 * 
 * @author Vu An Hoa
 */

relation idexc(int[] a, int[] b, int i, int j) == 
	forall(k : (i<=k & k<=j | a[k] = b[k])).

// relation idexptwopts(int[] a, int[] b, int i, int j) == 
// 	forall(k : (k = i | k = j | a[k] = b[k])).

relation bnd(int[] a, int i, int j, int low, int high) == 
	(i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

// is lemma below needed?
// bnd(a,i,j,low,high)  & i<=s & b<=j => bnd(a,s,b,low,high) 
// how to ensure permutation?

relation sorted(int[] a, int i, int j) == 
	(i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

// why is a'[n]=a[n] | a'[n]=a[n-1] needed?
    void insertelm(ref int[] a, int n, int low, int high)
	requires [t] dom(a,0,t) & 0 <= n & n <= t & sorted(a,0,n-1) 
                 & bnd(a,0,n,low,high)
	case {
		n <= 0 -> 
          ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n) 
              & a'=a 
              & bnd(a',0,n,low,high) //'
              ;
		n > 0 -> 
        case {
          a[n]<a[n-1] -> 
            ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
              & a'[n]=a[n-1]
              & bnd(a',0,n,low,high) //'
              ;
          a[n]>=a[n-1] -> 
            ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
              & a'[n]=a[n]
              & bnd(a',0,n,low,high) //'
              ;
        }
          //& (a'[n] = a[n] | a'[n] = a[n-1]);
	}
{
	if (n > 0) { 
		if (a[n] < a[n-1]) {
			int temp = a[n];
			a[n] = a[n-1];
			a[n-1] = temp;
			insertelm(a,n-1,low,high);
		}
	}
}

void insertelm2(ref int[] a, int n)
	requires [t] dom(a,0,t) & 0 <= n & n <= t & sorted(a,0,n-1)
    //& bnd(a,0,n,low,high)
	ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
    //& bnd(a',0,n,low,high)
    ;


/* Sort a[0..n] using Insertion sort algorithm */
void insertion_sort(ref int[] a, int n)
	requires [t] dom(a,0,t) & 0<=n<=t 
        //& bnd(a,0,n,low,high)
	ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
        //& bnd(a',0,n,low,high)
         ;
	requires [t] dom(a,0,t) & 0<=n<=t 
    case {
     n<=0 -> ensures a'=a & dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
             ;
     n>0 ->  ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n)
             ;
    }
{
	if (n > 0) {
		insertion_sort(a,n-1);
		insertelm2(a,n);
	}
}

/* 
insertelm2 used
Total verification time: 2.036126 second(s)
	Time spent in main process: 0.392024 second(s)
	Time spent in child processes: 1.644102 second(s)

insertelm used
Total verification time: 2.428151 second(s)
	Time spent in main process: 0.420026 second(s)
	Time spent in child processes: 2.008125 second(s)
*/
