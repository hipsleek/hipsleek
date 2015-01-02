// pass-by-value
data pair {
  int x;
  int y;
}

data pair_star {
  pair deref;
}

int goo(pair_star@C q)
  requires q::pair*<r> * r::pair<a,b>
  ensures q::pair*<r> * r::pair<a,b> & res=a;
{
  return q.deref.x;
}


// naive alternative_translation 
int goo2(pair q)
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a;
{
  pair_star addr_q = new pair_star();
  addr_q.deref=q;
  return addr_q.deref.x;
}

// efficient alternative_translation 
int goo2(pair q)
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a;
{
  return q.x;
}

