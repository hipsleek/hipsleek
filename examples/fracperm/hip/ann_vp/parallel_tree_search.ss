/*
  Search for a value in a tree in parallel.
  Need flags "-tp mona -perm none" to enable mona prover
*/

/* representation of a node */

data node {
	int val;
	node left;
	node right; 
}

tree<S> == self = null & S = {}
	or self::node<v, p, q> * p::tree<S1> * q::tree<S2> & S = union(S1, S2, {v});

//sequential search
void search(node t,int v,ref bool result)
  requires t::tree<S> & @full[result] & @value[t,v]
  ensures t::tree<S> & !result' & forall (a1: (a1 in S | a1!=v)) & @full[result]
          or t::tree<S> & result' & exists (a2: (a2 in S | a2=v)) & @full[result];
{
  if (t==null){
    result=true;
  }else{
    if (t.val==v){
      result = false;
    }else{
      bool result1,result2;
      /* dprint; */
      search(t.left,v,result1);
      /* dprint; */
      search(t.right,v,result2);
      result= result1 || result2;
    }
  }
}

//parallel search - 1 thread
void para_search(node t,int v,ref bool result)
  requires t::tree<S> & @full[result] & @value[t,v]
  ensures t::tree<S> & !result' & forall (a1: (a1 in S | a1!=v)) & @full[result]
          or t::tree<S> & result' & exists (a2: (a2 in S | a2=v)) & @full[result];
{
  if (t==null){
    result=true;
  }else{
    if (t.val==v){
      result = false;
    }else{
      bool result1,result2;
      int id;
      /* dprint; */
      id = fork(para_search,t.left,v,result1);
      /* dprint; */
      para_search(t.right,v,result2);
      join(id);
      result= result1 || result2;
    }
  }
}

//parallel search - 2 thread
void para_search2(node t,int v,ref bool result)
  requires t::tree<S> & @full[result] & @value[t,v]
  ensures t::tree<S> & !result' & forall (a1: (a1 in S | a1!=v)) & @full[result]
          or t::tree<S> & result' & exists (a2: (a2 in S | a2=v)) & @full[result];
{
  if (t==null){
    result=true;
  }else{
    if (t.val==v){
      result = false;
    }else{
      bool result1,result2;
      int id1,id2;
      /* dprint; */
      id1 = fork(para_search2,t.left,v,result1);
      /* dprint; */
      id2 = fork(para_search2,t.right,v,result2);
      /* dprint; */
      join(id1);
      join(id2);
      result= result1 || result2;
    }
  }
}

