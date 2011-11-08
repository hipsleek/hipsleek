/*
 * Simple example: build a list with only 1s and finally a 0 (arbitrary length); 
 * afterwards, go through it and check if the list does have the correct form, and in particular
 * finishes by a 0.
 */
data node {
  int val;
  node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

node create(int n)
  requires n >= 0
  ensures res::lseg<r, n+1, S> * r::node<0,null> ;//& forall (b : (b notin S | b=1));
{  
    if (n==0) 
    { 
      return new node(1, new node(0,null)); 
    }
    else
    {   
      node tmp = create(n-1);   
      return new node(1,tmp);
    }
}


