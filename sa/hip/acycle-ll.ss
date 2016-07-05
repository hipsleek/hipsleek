data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).


void foo(ref node x)
 infer [H,G]
 requires H(x)
 ensures  G(x,x'); //'
 {
   node y = x;
   while (x != null) {
     x = x.next;
   }
 }




/*


void foo$node(  node x)
static  ((None,[]),EInfer [H,G]
              EBase H(x)&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 64::ref [x]
                                G(x,x')&true&{FLOW,(22,23)=__norm}[])
dynamic  EBase hfalse&false&{FLOW,(22,23)=__norm}[]

ref x
{
node y_20;
y_20 = x;
{
127::f_r_524_sa_hip_acycle-ll_ss_17_3$node~node(y_20,x)
}
}


*/
