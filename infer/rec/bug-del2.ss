
void del(int n)
  infer [n]
  requires true
  ensures  true; 
{  
    acc(n);
    n=n-1; 
    dprint;
    acc(n);
}

void acc(int n)
  requires n>=1
  ensures true;


void acc2(int n)
  requires n>=2
  ensures true;

/* TODO:
Why is 2<=n & 1<=n inferred but
only 1<=n is added to the NEW SPECS?
Why is 2<=n & 1<=n inferred but
only 1<=n is added to the NEW SPECS?


Inferred Pure:[ 2<=n, 1<=n]
OLD SPECS:  EInfer [n]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 1<=n & {FLOW,(20,21)=__norm}
         EAssume 1::
           true & 2<=n & {FLOW,(20,21)=__norm}


*/
