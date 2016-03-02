data node {
  int h;
  node n;
}

HeapPred H(node a).
  HeapPred G(node a, node b).


void while_loop (ref int i, ref node p, ref node t)
    infer [H,G] requires H(p) ensures G(p,p'); //'
{
   if  (i >= 10) return;
   else {
    i++;
   //H(p) ==> p|-><_,n> * HP(n)
    p.h = 1;
   // p|-><1,n> * HP(n)

    t = new node(0,null);//(List) malloc(sizeof(struct node));
  // p|-><_,n> * HP(n) * t|-><_,_>

    //if (t == 0) exit(1);

    p.n = t;
  //HP(t) ==> t|-><_,q> * HP1(q)
  // p|-><_,t> * t|-><_,q> * HP1(q)

    p = p.n;
// p|-><_,t> *  t|-><_,q> * HP1(q) & p'=t //'
// p|-><_,t> * t|-><_,q> * HP1(q) & p'=t ==> H(p')
    return while_loop (i, p, t);
   }
 }

/*
H(p) ==> p|-><_,n> * HP(n)
//new/malloc. concretize unknown heap --> known heap
HP(t) ==> t|-><_,q> * HP1(q)

p'|-><_,q> * HP1(q) ==> H(p')

 */
