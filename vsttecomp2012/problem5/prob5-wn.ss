// below is hard to support in current system
// most likely need array to handle this example

data node {
  int val;
  node next;
}

data graph {
  int vertex;
  node succlst;
  graph next;
}

contains<d,r> ==
     self=null & !r
  or self::node<v,_> & v=d & r
  or self::node<v,n> * n::contains<d,r> & v!=d 
  inv true;
/*
Exception occurred: Failure("Presburger.b_apply_one_term: attempting to substitute arithmetic term for boolean var")
*/

/*
arc<s,d,r> ==
  self::graph<i,l,n> * l::contains<d,r> & s=i
  or self::graph<i,l,n> * n::arc<s,d,r> & s!=i
  or self=null & !r
  inv true;
*/
