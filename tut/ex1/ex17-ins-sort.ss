data node {
  int val;
  node next;
}

lsort<S> == emp & self=null & S={}
  or self::node<v,q>*q::lsort<S1> & S=union({v},S1)
          & forall (w:(w notin S1| v<=w))
  inv true;

node insert(node x, node y)
  requires x::node<v,null> * y::lsort<S>
  ensures res::lsort<S2> & S2=union({v},S);
{
  if (y==null) return x;
  else 
    if (x.val<=y.val) {
      x.next=y; return x;
    } else {
      node tmp = insert(x,y.next);
      y.next = tmp;
      return y;
    }
}

/*
# ex17-ins-sort.ss

Which prover are we using? mona, z3 or oc?
 init_tp not executed?

It seems that pure_tp="om" by default in tpdispatcher.ml.
However, when we use -tp om, there is a error message 

pls2nus@loris-laptop:~/code/default/tut/ex1$ ../../hip ex17-ins-sort.ss -tp om
WARNING : Command for starting the prover (mona) not found

!!!Full processing file "ex17-ins-sort.ss"
Parsing file "ex17-ins-sort.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting Omega.../usr/local/bin/oc

!!!  xxxx bag: :bagOmega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: bag or list constraint")
 Formula: exists(S1:exists(v:S=union({v},S1) & forall(w:(w <notin> S1  | v<=w))))

Checking procedure insert$node~node... 
Procedure insert$node~node SUCCESS.
Stop Omega... 65 invocations 
0 false contexts at: ()



*/
