data node{
	int val;
	node next;
}

ll<p, n> == self = p & n = 0  
            or self::node<_, r> * r::ll<p, m> & n = m+1 //& self != p
            inv n >= 0;


ll0<n> == self = null & n = 0 
	or self::node<_, q> * q::ll0<n-1>; 

sll<n, sm, lg> == self::node<qmin, null> & qmin = sm & qmin = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n-1, qs, lg> & q != null & sm <= qs 
               inv n >= 1 & sm <= lg;

/* view for bounded lists */
bndl<n, sm, bg> == self = null & n = 0 & sm <= bg
	or self::node<d,p> * p::bndl<n-1, sm, bg> & sm <= d & d <= bg  
	inv sm <= bg & n >= 0;

void id3(node x, node p, node r,int n)
	requires x::ll<p, n>   
	ensures r::ll<p,j> * x::ll<r, i> & n=i+j ; // & (i=0 & x=r' or i>0 & x!=r') ;
{

	if (x == p)
	{
           if (x==r) {
		 skip();
                 //assert n=0 & i=0 ;
		 //assume false;
           } else assume false;
	}
	else {
		if (x==r) {
                        skip();
		        //assume false;
                } else
                   {
			bind x to (v, z) in 
			{
  				//dprint;
				id3(z, p ,r,n-1);
			}
                        //assume x!=r';
  			//dprint;
                        //assert r'::ll<p,_> ;
                        //assert x'::ll<_,k> & k>0;
                        //assert x'::node<_,_>;
			//assume false;
                   }
	}
}

void id3a2(node x, node p, node r, int n, int i, int j)
	requires x::ll<r, i> * r::ll<p, j> & n=i+j & i>=0 & j>=0
	ensures x::ll<p, n>;
{
	if (x==r) {
		if (i!=0) {
			id3a2(x.next, p, r, n-1, i-1, j);
		}
	}
	else {
		id3a2(x.next, p, r, n-1, i-1, j);
	}
}

void id3a2r(node x, node p, ref node r, ref int n, ref int i, ref int j)
	requires x::ll<p, n>
	ensures x::ll<r', i'> * r'::ll<p, j'> & n=i'+j' & i'>=0 & j'>=0;
{
	if (x==p) {
		if (n!=0) {
			assume false;
		}
		else {
			r = x;
			i = 0;
			j = 0;
			n = 0;
			//assert x::ll<r', i'> * r'::ll<p, j'> & n=i'+j' & i'>=0 & j'>=0; 
		}
	}
	else {
		assume false;
	}
}

void lbreak(node x)
	requires x::ll<p, n>
	ensures x::ll<q, n1> * q::ll<p, n2>;
{
}

void id3a3r(node x, node p, int n, int i, int j, ref node r)
	requires x::ll<p, n> & i+j=n & i>=0 & j>=0
	ensures x::ll<r', i> * r'::ll<p, j>;
{
	if (i==0) {
/*
		if (n==0) {
			r = x;
			//assert x::ll<r', 0> * r'::ll<p, 0>;
		}
		else {
			r = x;
			//dprint;
			assert r'=x;
			assert x::ll<r', 0>;
			assert r'::ll<p, n>;
			assert x::ll<r', i> * r'::ll<p, j>;
		}
*/
		r=x;
	}
	else {
		id3a3r(x.next, p, n-1, i-1, j, r);
		//assume false;
	}
} 

void id3a4r(node x, node p, int n, int i, int j)
	requires x::ll<p, n> & i+j=n & i>=0 & j>=0
	ensures x::ll<r, i> * r::ll<p, j>;
{
	if (i==0) {
		//assert x::ll<r, i> * r::ll<p, j> & i=0 & j=n;
	}
	else {
		//assert x::ll<r, i> * r::ll<p, j> & i=0 & j=n;
		//id3a4r(x.next, p, n-1, i-1, j);
		assume false;
	}
} 

bool choice() requires true ensures true;

void id3a3(node x, node r, int n, int i)
	requires x::ll<r, i> * r::ll<p, j> & n=i+j
	ensures x::ll<p, n>;
{
	if (x==r) {
		if (i!=0) {
			id3a3(x.next, r, n-1, i-1);
		}
	}
	else {
		id3a3(x.next, r, n-1, i-1);
	}
}


void id3a(node x, node p, node r, int n, int i, int j)
	//requires x::ll<p, n> & n=i+j & i>=0 & j>=0 & n>=0
	//ensures r::ll<p,j> * x::ll<r, i> ; 
	requires r::ll<p,j> * x::ll<r, i> & n=i+j & i>=0 & j>=0 & n>=0 
	ensures x::ll<p, n> ; 
	//requires x::ll<r, i> * r::ll<p, j>   & n=i+j
	//ensures x::ll<p, n>;
{
        if (x==r) {
			assert i=0;
			assert x::ll<p, j>;
			skip(); 
			//assume false;
		}
        else { bind x to (v, z) in 
               { if (z==r) {
					skip(); 
					assume false; 
				}
                 else {id3a(z, p ,r,n-1,i-1,j); };
               };
        }
}

void skip() requires true ensures true;
bool rand() requires true ensures true;

void id1(node x, int s, int l)
	requires x::sll<n, i, j> & n>0 & s<=i & l>=j
	ensures x::bndl<n, s, l>;
{
	bind x to (v, z) in 
	{
		if (z != null) 
		{
			id1(z,s,l);
			//assume false;
		}
		else
			skip();
			//assume false;
	}
}

void id2a(node x,int s)
	requires x::sll<n, i, j> & n>0 & s<=i
	ensures x::bndl<n, s, l> & l>=j;
{
	bind x to (v, z) in 
	{
		if (z != null) 
		{
			id2a(z,s);
			//assert z'::bndl<n-1, s1, l1> & l1>=j & s1<=zi;
			//assume false;
		}
		else
			skip();
			//assume false;
	}
}

/*
// does not work
void id2(node x)
	requires x::sll<n, i, j> & n>0
	ensures x::bndl<n, s, l> & s<=i & l>=j;
{
	bind x to (v, z) in 
	{
		if (z != null) 
		{
			id2(z);
			assert z'::bndl<n-1, s1, l1> & l1>=j & s1<=zi;
			//assume false;
		}
		else
			skip();
			//assume false;
	}
}
*/
