struct node {
  struct node* left;
  struct node* right;
};

/*@
HeapPred H(node x).
HeapPred G(node y).
*/
int rand()
/*@
  requires true
  ensures true;
*/
{
  return 1;
}

/*@
tree<> == self=null
 or self::node<l,r>*l::tree<> * r::tree<>;
*/
void trav(struct node* x)
/*@
  infer [H,G]
  requires H(x)
  ensures G(x);
*/
/*
  requires x::tree<>
  ensures x::tree<>;
*/
{  if (x) {
     if (rand()) x = x->left;
     else x = x->right;
     trav(x);
   }
}

/*
# cyc-tree-1.ss
 
Relational Assumptions:

[ // BIND
(1;1;0)  
   H(x) & x!=null --> x::node<left_25_881,right_25_882>@M 
     * HP_883(left_25_881) * HP_884(right_25_882),
 // BIND
(2;1;0)
   H(x) & x!=null --> x::node<left_26_889,right_26_890>@M 
     * HP_891(left_26_889) * HP_892(right_26_890),
 // PRE_REC
(1;1;0) HP_883(left_25_881) --> H(left_25_881),
 // PRE_REC
(2;1;0) HP_892(right_26_890) --> H(right_26_890),
 // POST
(1;1;0)
    HP_884(right_25_882) * x::node<left_25_881,right_25_882>@M 
     * G(left_25_881) --> G(x),
 // POST
(2;1;0)
    HP_891(left_26_889) * x::node<left_26_889,right_26_890>@M 
     * G(right_26_890) --> G(x),
 // POST
(2;0) H(x) & x=null --> G(x)]

It seems like we have lose some precision to obtain below.
I think we should currently only do so under some commands
option, such as --pred-unify-pre (to strengthen pre by 
unification of some branches).

Predicates
==========
[ G(x_921) ::= 
     H(left_25_881) * x_921::node<left_25_881,right_25_882>@M 
            * G(right_25_882)
     or emp&x_921=null
 ,
 H(x_920) ::= 
     x_920::node<left_25_898,right_25_899>@M * H(left_25_898) 
           * H(right_25_899)
     or emp&x_920=null
 ]

I would expect firstly:
   H(x) ::= emp & x=null 
    or x::node<left_25_881,right_25_882>@M 
           * H(left_25_881) * HP_884(right_25_882),
    or x::node<left_26_889,right_26_890>@M 
           * HP_891(left_26_889) * H(right_26_890),

   G(x) ::= emp & x=null 
    or HP_884(right_25_882) * x::node<left_25_881,right_25_882>@M 
       * G(left_25_881) 
     or HP_891(left_26_889) * x::node<left_26_889,right_26_890>@M 
     * G(right_26_890) --> G(x),

 --pred-unify-pre would then give:
   H(x) ::= emp & x=null 
    or x::node<left_25_881,right_25_882>@M 
           * H(left_25_881) * H(right_25_882),
   G(x) ::= emp & x=null 
    or H(right_25_882) * x::node<left_25_881,right_25_882>@M 
       * G(left_25_881) 
     or H(left_26_889) * x::node<left_26_889,right_26_890>@M 
     * G(right_26_890) --> G(x),

  --pred-unify-post would then give:
     G(x) ::= H(x)

--sa-dnc seems to produce what we expected above

Predicates
==========
[ G(x_902) ::=
    (1;1;0) HP_884(right_25_882) * x_902::node<left_25_881,right_25_882>@M 
      * G(left_25_881)
   \/ (2;1;0) HP_891(left_26_889) * x_902::node<left_26_889,right_26_890>@M 
      * G(right_26_890)
   \/ (2;0) emp&x_902=null,

H(x_901) ::=(1;1;0) H(left_25_898) * x_901::node<left_25_898,right_25_899>@M 
     * HP_884(right_25_899)
   \/ (2;1;0) H(right_26_905) * x_901::node<left_26_904,right_26_905>@M 
     * HP_891(left_26_904)
   \/ (2;0) emp&x_901=null,
 
HP_884(right_25_882) ::=(1;1;0) NONE,
HP_891(left_26_889) ::=(2;1;0) NONE]


*/
