/*data node {
  // can we annotate fields?
  int val;
  node next;
}*/

pred_prim sec<i : int>;

//global int i; // can we annotate i to say it's L or H?

//global set(boolean) Flow;

pred_prim security<h:int>;

int copy(int i) 
     requires i::security<r>@L
     ensures res=i;
{
  return i;
}

int plus(int i,int j) 
  requires i::security<r1>@L * j::security<r2>@L
  ensures  res::security<r3> & res=i+j & (r3<=r1 | r3<=r2)
  ;



int inc(int i) 
  requires i::security<r>@L
  ensures res::security<r> & res=i+1;
{
  return i+1;
}
