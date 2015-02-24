data node {
	int val;
	node next
}

view bnd<n,sm,bg> = 
 		self==null & n=0
   	or	self::node<d,p> * p::bnd<n-1,sm,bg> & sm <= d < bg 
	with n >= 0

view bnd2<n,d,sm,bg> = 
 		self==null & n=0
   	or	ex s2,b2. (self::node<d,p> * p::bnd2<n-1,_,s2,b2>  & sm <= d < bg & sm<=s2 & bg>=b2)  
   	//or	self::node<d,p> * p::bnd2<n-1,_,sm1,bg1> & sm>=sm1 & bg1<=bg & sm <= d < bg 
	with n >= 0

view sll<n, sm, lg> = 
		self::node<sm, q> & q==null & sm=lg & n=1 
	or	self::node<sm, q> * q::sll<n-1, qs, lg> & !(q==null) &  sm<=qs 
	with n>=1 & sm<=lg

view ll2<n, sm, lg> = 
		self::node<sm, q> & q==null & sm=lg & n=1 
	or	ex s2,l2. (self::node<d, q> * q::ll2<n-1, s2, l2> & !(q==null) &  sm=min(d,s2) & lg=max(d,l2))
	with n>=1 & sm<=lg

view bnd3<n,d> = 
 		self==null & n=0 
	or	self::node<d,p> * p::bnd3<n-1,_>  
	with n >= 0

view ll<$p,n> =
	self==p & n=0 
    or	ex $r,m,$q. (self::node<_,r>*r::ll<q,m> & p==q & n=m+1 & !(self==p))
        with n>=0
           
node idbnd(node xs) where
    xs::bnd3<n,d> & n>0 ; ex sm,lg. (res::bnd2<n,_,sm,lg>)
    //ex sm,lg. (res::ll2<n,sm,lg>)
{
   bool b;
   bind xs to (_,xn) in
   {
      b=is_null(xn);
      if b then {xn=null;
                 xs;}
      else { //node_error();
             xn=idbnd(xn);
             xs;
           }
   }
}

node empty() where
   true ; ex $p. (res::ll<p,1> & p==null);
{ 
  node x;
  x=null;
  x;
}

node idDist2(node xs, node y) where
    xs::ll<r,j> * y::ll<p,i> & r==y;
   //ex $r. (xs::ll<r,j> * y::ll<p,i> & r==y);
    ex m. (res::ll<p,m> & res==xs & m=i+j) ;
{
 bool b;
 b=eq(xs,y);
 if b then { 
       y; 
       dprint;
       //node_error();
 } else {
   b = havoc();
   if b then {
      //xs;
      node_error();
   } else {
          bind xs to (d,xn) in
           {
             //idDist2(xn,y);
             node_error();
           }
        }
 }
}

node idDist(node xs, node y) where
    xs::ll<p,n> & y==p ;
    ex $r,i,j. (res::ll<p,j> * xs::ll<r,i> & r==res & n=i+j)
{
 bool b;
 b=eq(xs,y);
 if b then { xs; }
 else {
   b = havoc();
   if b then {
      xs; 
      //node_error();
   } else {
          bind xs to (d,xn) in
           {
             idDist(xn,y);
             //node_error();
           }
        } 
 }
}
bool eq(node x, node y) where
   true; x==y & res=1 or !(x==y) & res=0.
bool havoc() where
   true; 0<=res<=1.

node id(node xs) where
   xs::sll<n,sm,lg> ; ex s2,l2. (res::bnd2<n,sm,s2,l2> & s2=sm & l2>lg);
   //xs::sll<n,sm,lg> ; res::bnd3<n,sm>;
   // res::bnd2<n,sm,_,_>;
   // forall s3. s3>lg => res::bnd<n,sm,s3>);
{  
   bool b;
   bind xs to (_,xn) in
   {
      b=is_null(xn);
      if b then {xn=null;
                 xs;}
      else { //node_error();
             xn=id(xn);
             xs;
           }
   }
}

node id2(node xs) where
   // xs::bnd3<n,d> ; res::bnd2<n,d,_,_>;
    xs::bnd2<n,d,_,_> ; res::bnd3<n,d>;
{  
   bool b;
   b=is_null(xs);
   if b then {
     xs;
     //assert ex s,l. (xs'::bnd2<n,_,s,l>);
   } else {
     bind xs to (_,xn) in
     {
       //assert xn'::bnd3<n-1,_>;
       xn=id2(xn);
       //assert xn'::bnd2<n-1,_,_,_>;
       //node_error();
       xs;
     }
     //assert ex m. (xs'::bnd2<m,_,_,_> & n=m);
     //assert xs'::bnd2<n+0,_,_,_>;
     //assert xs'::bnd2<n,_,_,_>;
     //assert ex s,l. (xs'::bnd2<n,_,s,l>);
     //dprint;
   }
}

bool bubtest(node xs) where 
	xs::bnd3<n,sm> & n>0;
	xs::sll<n,sm,_> & res=0 or xs::bnd3<n,_> & res = 1 
	//xs::sll<n,s2,l2> & res=0 & sm<=s2 & l2<lg or  
	//	 xs::bnd<n,sm,lg> & res = 1 
{
	bool b, flag, tmp, f, t; 
	int aux, one, zero;

	one = 1; 
	zero = 0;
	f = fvalue();
	t = tvalue();
	bind xs to (d,xsn) in {
		b = is_null(xsn);
		if b then {
			flag=f;
                        //error();
		} else {
                        flag=t;
                }
                //flag;
                my_or(f,flag);
        dprint;
         assert ex y. (xsn'::bnd<y,sm,lg> );
         }
         //dprint;
}
bool idbool(bool x) where true;x=0 & res=0 or x=1 & res=1.


node idB(node x) where 
   x::sll<n,s,l> ; ex l2. (res::bnd<n,s,l2> & l2>l) 
// x::sll<n,s,l> ; ex s2,l2. (res::bnd<n,s2,l2> & s2<=s & l2>l) 
{
   bool b;
   bind x to (d,xn) in {
      b=is_null(xn);
      if b then
          { x; 
         assert ex s3,l3. (xn'::bnd<_,s,l3> & s=d' & l3>l);
          }
      else { 
         //error_node();
         xn=idB(xn); x;
         assert ex l3,s3.(xn'::bnd<n-1,s3,l3> & s3=s & l3>l & s3<=d'& d'<l3  );
         assert ex l3.(xn'::bnd<n-1,s3,l3> & /* s=s3 &*/ l3>l & /*s3<=d'&*/ d'<l3  );
         assert ex l3.(xn'::bnd<n-1,s,l3> & l3>l & s<=d'& d'<l3  );
      }
   }
   //dprint;
}

node error_node() where true; false.
bool my_or(bool x,bool y) where 0<=x<=1 & 0<=y<=1;x=0 & res=y or x=1 & res=1.

bool bubble(node xs) where 
	xs::bnd2<n,sm,s,l> & n>0;
	//xs::bnd3<n,sm> & n>0;
	exists lg. (xs::sll<n,sm,lg> & s<=sm & lg<l & res=0) or 
         exists s2,l2. (xs::bnd2<n,_,s2,l2> & s2<=sm & l2>=l & res = 1 )
	//xs::bnd2<n,s2,sm,lg> & 0<=res<=1
	//xs::bnd2<n,s2,sm,lg> & 0=res or xs::bnd2<n,_,sm,lg> & res=1
	//xs::bnd2<n,s2,sm,lg> & res=0  or ex s3. (xs::bnd2<n,_,sm,lg> & res = 1) 
	//xs::sll<n,s2,_> & res=0 & sm<=s2 & l2<lg or xs::bnd2<n,_,_,_> & sm<=s2 & res = 1 
{
	bool b, flag, tmp, f, t; 
	int aux, one, zero;

	one = 1; 
	zero = 0;
	//f = lt(one,zero);
	//t = lt(zero,one); 
	bind xs to (d,xsn) in {
		b = is_null(xsn);
		if b then {
			fvalue();
		} else {
			tmp = bubble(xsn);
			bind xsn to (e,xsnn) in {
				b = lte(d,e);
				if b then {
					flag = fvalue();
                                        //verror();
				}	
				else {
					aux = d;
					d = e;
					e = aux;
					flag = tvalue();
                                        if tmp then {
                                           skip();
                                           //assert xsnn'::bnd3<n-2,_>;
                                           //verror();
                                        } else {
				           b = is_null(xsnn);
                                           if b then {
                                              skip();
                                           } else {
                                           //dprint;
                                           //assert xsnn'::sll<n-2,_,_> or xsnn'::bnd3<n-2,_>;
                                           assert xsnn'::sll<_,_,_>;
                                           //assert xsnn'::bnd3<_,_>;
                                           xsnn = id(xsnn);
                                           //verror();
                                           }
                                        }
                                        //verror();
				} 
			}
                        //dprint;
                        //assert ex p1,p2. (xsn'::bnd<y,p1,p2> & p1=sm & p2=lg & y=n-1);
                        //assert ex y,p1,p2. (xsn'::sll<y,p1,p2> & y=n-1);
                        //dprint;
			my_or(flag,tmp);
                        //assert res=0 or res=1;
                        //assert xsn'::sll<n-1,_,_> & res=0 or xsn'::bnd2<n-1,_,_,_> & res=1 ;
                        //assert ex p.(xsn'::bnd2<n-1,_,_,_> &p=s2 & res=0)  or xsn'::bnd2<n-1,_,_,_>&res=1  ;
		}
	} 
        //dprint;
        //assert xs'::bnd2<_,_,_,_>;
        //assert res=0 ;
        //assert xs'::bnd2<n,_,_,_>& res=1;
        //assert xs'::sll<_,_,_> & res=0;
        //assert res=0 or res=1 ;
}

void bsort(node xs) where
	xs::bnd2<n,_,sm,lg> & n>0;
	exists s,l. (xs::sll<n,s,l> & sm<=s & l<lg )
{
   bool b;
   b = bubble(xs);
   if b then {
      bsort(xs);
   } else {
      skip();
   }
}

/* function to implement bubble sort 
bool bubble(node xs) where 
	xs::bnd<n,sm,lg> & n>0;
	xs'::sll<n,s2,l2> & res=0 & sm<=s2 & l2<lg or  
		 xs'::bnd<n,sm,lg> & res = 1 
{
	bool b, flag, tmp, f, t; 
	int aux, one, zero;

	one = 1; 
	zero = 0;
	f = lt(one,zero);
	t = lt(zero,one); 

	bind xs to (d,xsn) in {
		b = is_null(xsn);
		if b then {
			f;
		}
		else {
			bind xsn to (e,xsnn) in {
				b = lte(d,e);
				if b then {
					flag = f;
				}	
				else {
					aux = d;
					d = e;
					e = aux;
					flag = t;
				} 
			}
			tmp = bubble(xsn);
			my_or(flag,tmp);
			flag;
		}
	} 
}
*/

bool fvalue() where true;res=0.
bool tvalue() where true;res=1.
void verror() where true;false.
void skip() where true;true.
bool error() where true;false.

bool check(node x) where 
	x::bnd<n,sm,lg> & n > 0;
	x::sll<n,s2,l2> & res = 1 /*& s2>=sm & l2<lg*/
	or x::bnd<n,sm,lg> & res = 0
{
	bool f,t,b;
	int o, z;

	o = 1;
	z = 0;
	f = lt(o,z);
	t = lt(z,o);
	
	bind x to (v,xn) in {
		b = is_null(xn);
		if b then {
			t;
		}
		else {
			bind xn to (xv,xnn) in {
				b = lte(v,xv);
			}
			if b then {
				check(xn);
			}
			else {
				f;
			}
		}
	}
}
	
bool bubbleup(node xs) where 
	xs::bnd<n,sm,lg> & n>0;
	//xs::sll<n,s2,l2> & res = 0 & s2>=sm & l2<lg or
	xs::bnd<n,sm,lg> & res = 0 or
	xs::bnd<n,sm,lg> & res = 1

{
	bool b, flag, tmp, f, t; 
	int aux, one, zero;

	one = 1; 
	zero = 0;
	f = lt(one,zero);
	t = lt(zero,one); 

	bind xs to (d,xsn) in {
		b = is_null(xsn);
		if b then {
			f;
		}
		else {
			bind xsn to (e,xsnn) in {
				b = lte(d,e);
				if b then {
					flag = f;
				}	
				else {
					aux = d;
					d = e;
					e = aux;
					flag = t;  
				} 
			}
			tmp = bubbleup(xsn);		
			my_or(flag,tmp);    
		}
		
	} 
}




node node_error() where true; false.
import "primitives"

data node {
	int val;
	node next;
}

data node2 {
	int val1;
	bool val2;
	node2 p1;
	node2 p2;
}

/*
node id(node x) 
	requires x::node<v, r> ensures x::node<v, r> & res=x;
{
	return x;
}

node test1(int x, node y)
	requires true ensures res::node<a, b> & a=x & y=b;
{
	return new node(x, y);
}

node test2()
	requires true ensures res::node<a, b> & a=0 & b=null;
{
	int a = 1;
	return new node(--a, null);
}
*/

node test3(node x)
	requires true ensures res=null or res::node<_,_>;
{
	if (x!=null) return x;
	
	return new node(0, null);
}
