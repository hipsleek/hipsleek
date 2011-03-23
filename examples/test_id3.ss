data node{
	int val;
	node next;
}

ll<p, n> == self::node<_, r> * r::ll<q, m> & p = q & n = m+1 & self != p
            or self = p & n = 0  
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
void id3a(node x, node p, node r, int n)
	requires x::ll<p, n> 
	ensures r::ll<p,j> * x::ll<r, i> & n=i+j ; 
	//requires x::ll<r, i> * r::ll<p, j>   & n=i+j
	//ensures x::ll<p, n>;
{
	if (x == p)
	{
		if (x==r){
		 skip();
		 //assume false;
		}
                else 
		assume false;
	}
	else {
		if (x != r)
			bind x to (v, z) in 
			{
				id3a(z, p ,r,n-1); //, n-1);
			}
		else  {
			skip();
		}
	}
}

void id3b(node x, node p, node r, int n)
	//requires x::ll<p, n> & x!=p
	//ensures r::ll<p,j> * x::ll<r, i> & n=i+j ; 
	requires x::ll<r, i> * r::ll<p, j>   & n=i+j & x!=p
	ensures x::ll<p, n>;
{
	if (x == r)
	{
		skip();
	}
	else {
		bind x to (v, z) in 
		{ if (z!=p) 
   		    id3b(z, p ,r,n-1); //, n-1);
                  else if (z!=r) assume false;
                  //{ skip(); 
                   //           assume false; 
                    //        }
		}
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
