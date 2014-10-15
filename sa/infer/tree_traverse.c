bool nondeterm()
 requires true
 ensures !res or res;

data node {
        int val;
        node left;
	node right
}

prepost for x!=null
 requires true
 ensures res & x!=null \/ !res & x=null

void traverse(ref node x)
requires H(x)
ensures G(x,x').//'
{
	if(x != null)
	{
		if(nondeterm()) x = x.left;
		else x = x.right;
		traverse(x);
	}
}

 //function call on x!=null
 [H,G] H(x) |- true --* b & x!=null \/ !(b) & x=null
  -->  H(x)&  b & x!=null
       or H(x)&  !b & x!=null

 //state after then branch
 [H,G] H(x)&  b & x!=null

 //function call on nondeterm()
 [H,G] H(x) & x!=null |- true --* !res v res;

//state after then branch
[H,G] H(x) & x!=null

//for x.left
[H,G] H(x) & x!=null |- x::node<v,l,r>
--> H1(x,l,r)*x::node<v,l,r> & x!=null
with H(x) -> H1(x,l,r)*x::node<v,l,r>

//post-cond then branch: 
[H,G,H1] H1(x,l,r)*x::node<v,l,r> & x!=null & x' = l //'

//state after else branch
[H,G] H(x) & x!=null

//post-cond else branch: 
[H,G,H1] H1(x,l,r)*x::node<v,l,r> & x!=null & x' = r //'

 //recursive function call
	  [H,G,H1] H1(x,l,r)*x::node<v,l,r> & x!=null & (x' = r v x' = r) 
    |- H(x') --* G(x',x") //"
  --> [H,G,H1] G(x0,x') * H1(x,l,r)*x::node<v,l,r> & (x0 = r v x0 = r)
   with H1(x,l,r)*x::node<v,l,r> & (x' = r v x' = l) -> H(x')

 //Postcondition
[H,G,H1] G(x0,x') * H1(x,l,r)*x::node<v,l,r> & (x0 = r v x0 = r)
     |- G(x,x')
  with G(x0,x') * H1(x,l,r)*x::node<v,l,r> & (x0 = r v x0 = r) -> G(x,x')

 //state after else branch
 [H,G] H(x)& x=null & x' = x  |- G(x,x')

inferred inductive predicates:
==============================
   H(x) -> H1(x,l,r)*x::node<v,l,r>
   H1(x,l,r)*x::node<v,l,r> & x' = r -> H(x')
   H1(x,l,r)*x::node<v,l,r> & x' = l -> H(x')
   G(x0,x') * H1(x,l,r)*x::node<v,l,r> & x0 = r -> G(x,x')
   G(x0,x') * H1(x,l,r)*x::node<v,l,r> & x0 = l -> G(x,x')
    H(x)& x=null & x' = x  -> G(x,x')

Normalize:

H(x) -> x=null v x::node<v,l,r> * H(r) * H(l)

   G(x0,x') * H1(x,l,r)*x::node<v,l,r> & x0 = r -> G(x,x')
   G(x0,x') * H1(x,x0,r)*x::node<v,l,r> & x0 = l -> G(x,x')
    H(x)& x=nullx' = x  -> G(x,x')

G(x0,x') * H(x) -> G(x,x')
   G(x0,x') * H(x) -> G(x,x')
H(x)& x=null & x' = x -> G(x,x')

H(x) & x'=null ->  G(x,x')





