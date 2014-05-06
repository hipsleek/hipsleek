struct node{
  int val;
  struct node* next;
};

/*@
ll<> == self = null  or self::node<_, q> * q::ll<>;

lseg<p> == self = p & self!=null  or self::node<_, q> * q::lseg<p>& self!=p;
lshd<p> == p::lseg<self>*self::node<_,null>;
*/
/*@
HeapPred H(node a).
PostPred G(node a, node b).
*/
struct node* last (struct node* x)
// requires x::ll<> & x!=null ensures res::lshd<x>;
/*@
  infer[H,G] requires H(x) ensures G(res,x);
*/
{
   if (x->next==NULL) return x;
   else 
   {
	struct node* t = last(x->next);
	//t.val = t.val+1;
	struct node* v = t->next;
        //@	assert v' = null;
	return t;
	}
}
/*
# last-2.ss

[ H(x)&true --> x::node<val_18_812,next_18_813>@M * HP_4(next_18_813)&true,

 HP_4(next_18_813)&next_18_813!=null --> H(next_18_813)&true,

 HP_4(next_18_813)&next_18_813=null --> emp&true,

 G(t_37',next_18_813)&
  next_18_813!=null --> t_37'::node<val_23_830,next_23_831>@M * 
  GP_2(next_23_831,next_18_813@NI) * GP_3(next_18_813,t_37'@NI)&true,

 x::node<val_18_812,next_18_813>@M&res=x & next_18_813=null --> G(res,x)&true,
 x::node<val_18_812,next_18_813>@M * GP_3(next_18_813,res@NI) * 
  res::node<val_23_830,v_null_23_836>@M&next_18_813!=null & 
  v_null_23_836=null --> G(res,x)&true

====

[ H(x_862) ::=  x_862::node<val_18_812,next_18_813>@M * HP_4(next_18_813)&true,
 G(res_864,x_865) ::=  
 res_864::node<val_18_812,next_18_813>@M&next_18_813=null & res_864=x_865
 or x_865::node<val_18_866,next_18_867>@M * GP_3(next_18_867,res_864) * 
    res_864::node<val_18_812,next_18_813>@M&next_18_867!=null & 
    next_18_813=null
 ,
 HP_4(next_18_863) ::=  
 next_18_863::node<val_18_812,next_18_813>@M * HP_4(next_18_813)&true
 or emp&next_18_863=null
 ,
 GP_2(next_23_831,next_18_813) ::= NONE]


*/


