data node {
	int val;
	node next;
}

ll-shape(a)[Base,Rec,Inv]= Base(a,self)
  or self::node<v,q>* q::ll-shape(aq) & Rec(a,aq,v,self,q)
  inv Inv(a);
  
llBase (a,self) = self=null 
  
llsBase(a,self) = a=0 
llsRec(a,aq,v,self,q) = a=aq+1 
llsInv(a) = a>=0;
  
lsegBase (a,self) = self=a 
lsegRec (a,aq,v,self,q) = aq=a 
     
ll<n> = ll-shape<> [llsBase,llsRec,llsInv : n] [Base = llBase : ] 

lseg<n,p> = ll-shape<> [llsBase,llsRec,llsInv : n] [Base=lsegBase, Rec=lsegRec: p]
    
    // ll-part<n> = ll-shape<> [llsBase,llsRec,llsInv : n]
    // ll<n> = ll-part<n> [Base = llBase :]
    // lseg<n,p> = ll-part<n> [Base=lsegBase, Rec=lsegRec: p]
    
clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

/*
ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;
*/
void append(node x, node y)
  requires x::ll<n> & x!=null //& n>0
	ensures x::lseg<y, n>;
  requires x::ll<n> & y=x & n>0
	ensures x::clist<n>;
{
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

node app2(node x, node y)
/*
  requires x::lseg<null,n> 
  ensures res::lseg<y, n>;
*/

/*
requires x=null
ensures res=y ;
requires x::lseg<null,n> & x!=null
  ensures res::lseg<y,n>;
*/

 requires x::lseg<null,n> 
  ensures res=y & x=null & n=0// n=0
  or res::lseg<y,m> & res=x & x!=null & m=n & n>0; //m>0

/*
 case {
  x=null -> ensures res=y;
  x!=null -> requires x::lseg<null,n> 
             ensures res::lseg<y,n>;
 }
*/
{
  if (x==null) return y;
  //dprint;
  node tmp=x.next;
  //assume tmp'=null or tmp'!=null;
  x.next=app2(tmp,y);
  return x;
}

int test(int x)

  case {
   x>0 -> ensures res=1;
   x<=0 -> ensures res=3;
  }
/*
requires true
  ensures x>0 & res=1 
     or x<=0 & res=2;
*/{
 if (x>0) {return 1;}
 else {
   assert x>0;
   assert x<=1;
   if (x>2) 
     {return 2;}
   else 
     {return 3;}
 }
}     
