/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

void loop1(ref int i, int y) 
//  requires i>=0 & y<=0
//  ensures false;
//  requires i<0 
//  ensures i'=i; //'
 case {
  i<0 -> ensures "term": i'=i; //'
  i>=0 -> case {
  	y<=0 -> ensures "loop" : false; // loops
        y>0 -> ensures "term": true; // terminates
     } 
  }
{
  if (i>=0) { 
    i=i-y; 
    assert "term": (i+y)-(i'+y)>0;
    assert "term": i'+y>=0;
    loop1(i,y);
  }
}

int foo(int n) 
 case {
  n<0 -> ensures "nonterm" : false;
  // non-terminating inputs..
  n>=0 -> ensures "term" : res=2*n;
 }
// variance n
{ 
  if (n==0) return 0;
  else { 
        int m;
        m=n-1;
        assert n>m'; //'
        assert "term" : m'>=0;
        return 2+foo(m);
   }
}

int Ack(int m, int n)
case {
  m<0 -> ensures "nonterm_m" : false;
  m=0 -> ensures res=n+1;
  m>0 -> case 
          { 
		n<0 -> ensures "nonterm_n" : false;
            	n>=0 -> ensures "term" : res>0;
          }  
}
//requires n>=0 & m>=0
//ensures res>0;
// variance n,m
{ 
	if (m==0) return n+1;
    	else if (n==0) {
      		int m1=m-1;
      		assert "term" : m1'>=0 & m'-m1'>0; //'
       		return Ack(m1,1);
    	}
  	else {
    		int m1=m-1;
    		int n1=n-1;
    		assert "term" : m'=m' & n1'>=0 & n'-n1'>0; //'
    		int r = Ack(m,n1);
    		assert "term" : m'-m1'>0 & m1'>=0; //'
    		return Ack(m-1, r);
  	}
}

int gcd(int m, int n)
case {
	m <= 0 -> ensures "nonterm" : false;
	m > 0 -> case {
			n <= 0 -> ensures "nonterm" : false;
			n > 0 -> ensures "term" : res>0;
		 }
}	

{
   if (m > 0) {
   if(m == n) {
	  //assume false;
      return m;
   }
   else if (m > n) {
      int m1=m-n;
      //assert "term" : (m'+n')-(m1'+n')>0 & (m1'+n')>=0;
      return gcd(m1, n);
   }
   else {
      int n1=n-m;
      //assert "term" : (m'+n')-(m'+n1')>0 & (m'+n1')>=0;
      return gcd(m, n1);
   }
   }
   else {
     //assume false;
	return m;
   }
}

int perm1(int m, int n, int r)
case {
	r>0 -> ensures true; 
	r<=0 -> case {
			n>0 -> ensures true;
			n<=0 -> ensures res=m; 
		}
}
{
	if (r>0) {
		int r1=r-1;
		//assert r1'>=0 & r'-r1'>0;
		return perm1(m, r-1, n);
	}
	else if (n>0) {
		int n1=n-1;
		return perm1(r, n-1, m);
	}
	else 
		return m;
}






