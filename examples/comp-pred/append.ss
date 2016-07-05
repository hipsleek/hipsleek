data node[t] {
	t val;
	node next;
}

ho_pred ll_shape[t]<a:t2>[Base,Rec,I] == Base(a,self)
  or self::node[t]<v,q> * q::ll_shape[t]<aq> * Rec(a,aq,v,self,q) 
     inv I(self,a);

     
ho_pred ll_gshape[t]<a:t2>[Base,Rec,I] == 
     Base(a,self)
  or self::node[t]<v,q> * q::ll_gshape[t]<aq>
 * Rec(a,aq,v,self,q) 
     inv I(self,a); 

ho_pred ll_acyclic[t]<a:t2> extends 
ll_gshape[t]<a>
     with { Base(_,self) = self=null }

ho_pred ll_acyclic[t]<a:t2>[Base,Rec,I] ==
       ll_gshape[t]<a>[\ (a,self)-> self=null & Base(a,self), Rec, I];

ho-pred ll_seg[t]<(p:node[t],a:t2)> extends ll_gshape[t]<(p,a)>
       with { Base((p,_),self) = self=p; }

ho_pred ll_seg[t]<(p:node[t],a:t2)>[Base,Rec,I] ==
  ll_gshape[t]<(p:node[t],a:t2)>[\ ((p,a),self)-> self=p & Base((p,a),self), Rec, I];


ho_pred ll_seg_size[t]<(p:node[t],a:int)> extends ll_seg[t]<(p,a)>
       with { Base((p,a),self) = a=0;
               Rec((p,a),(_,a1),..) = a=a1+1; }

ho_pred ll_seg_size[t]<(p:node[t],a:int)>[Base,Rec,I]
  ll-seg[t]<a>[\ ((p,a),self)-> a=0 & Base((p,a),self), 
               \ ((p,a),(p1,a1),..) as args = a=a1+1 & Rec(ars),I ]
Rec, I];
       with { Base((p,a),self) = a=0;
               Rec((p,a),(_,a1),..) = a=a1+1; }

ho_pred ll_seg_size[t]<(p:node[t],a:t2)>[Base,Rec,I] ==
  ll_gshape[t]<(p:node[t],a:t2)>[\((p,a),self)-> self=p & Base((p,a),self), Rec, I];

ho_pred ll[t]<n> == self::ll-shape[t]<n>
  [\(n,_)-> n=0, \(n,n1,..)->n=1+n1, \(n,_)->n>=0];


ho_pred lseg<n,p> == ll-shape<> [llsBase,llsRec,llsInv : n] [Base=lsegBase, Rec=lsegRec: p];
    
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
