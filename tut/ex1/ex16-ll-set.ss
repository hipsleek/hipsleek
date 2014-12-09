data node {
  int val;
  node next;
}

ll<S> == emp & self=null & S={}
  or self::node<v,q>*q::ll<S1> & S=union({v},S1)
  inv true;

int length(node x)
  requires x::ll<S>
  ensures x::ll<S> & res>=0;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex16-ll-set.ss

Why am I getting this mona error in default branch?
Was it expecting mona to be in curent directory for svcomp14?

pls2nus@loris-laptop:~/code/default/tut/ex1$ ../../hip ex16-ll-set.ss -tp om
WARNING : Command for starting the prover (mona) not found

pls2nus@loris-laptop:~/code/default/tut/ex1$ ../../hip ex16-ll-set.ss -tp mona
WARNING : Command for starting the prover (mona) not found
pls2nus@loris-laptop:~/code/default/tut/ex1$ which mona
pls2nus@loris-laptop:~/code/default/tut/ex1$ which mona_inter
/usr/local/bin/mona_inter


Is the default tp auto? Did it try Omega
before mona? but which version of mona?

ls2nus@loris-laptop:~/code/default/tut/ex1$ ../../hip ex16-ll-set.ss 

!!!  xxxx bag: :bagOmega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  union({v},S1)")
 Formula: exists(S1:exists(v:S=union({v},S1)))

Checking procedure length$node... 
Procedure length$node SUCCESS.



*/
