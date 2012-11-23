data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

//valid
//x:write
//y:read but should be writable
void append(node x, node y)
  /* requires x::ll(1.0)<n> & x!=null //& n>0 */
  /* ensures x::lseg(1.0)<y, n>; //valid because we don't care y */

// we should have full permission to y because we tie up x and y
  requires x::ll(1.0)<n> * y::ll(1.0)<m> & n>0
  ensures x::ll(1.0)<e>& e=n+m;
{
  // dprint;
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

//fail
//x:write
//y:read but should be writable
void append2(node x, node y)
  requires x::ll(0.5)<n> & x!=null //& n>0
  ensures x::lseg(0.5)<y, n>; //valid because we don't care y

// we should have full permission to y because we tie up x and y
  /* requires x::ll(0.5)<n> * y::ll(0.5)<m> & n>0 */
  /* ensures x::ll(0.5)<e>& e=n+m; */
{
  // dprint;
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append2(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

//valid
//we write to x
node app2(node x, node y)

/*   requires x::lseg(1.0)<null,n> */
/*   ensures res::lseg(1.0)<y, n>; */

  /* requires x::lseg(1.0)<null,n> */
  /* ensures res=y & x=null & n=0// n=0 */
  /* or res::lseg(1.0)<y,m> & res=x & x!=null & m=n & n>0; //m>0 */

 case {
  x=null -> ensures res=y;
  x!=null -> requires x::lseg(1.0)<null,n>
    ensures res::lseg(1.0)<y,n>;
 }
{
  if (x==null) return y;
  //dprint;
  node tmp=x.next;
  //assume tmp'=null or tmp'!=null;
  x.next=app2(tmp,y);
  return x;
}
