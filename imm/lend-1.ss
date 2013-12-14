data pair{
 int fst;
 int snd;
}

int first(pair p)
 requires p::pair<v@L,_@A>
 ensures res=v;
{
 return p.fst;
}



int main(pair p)
 requires p::pair<v,a>
 ensures p::pair<v,a> & res=v;
{
  dprint;
  int t = first(p);
  dprint;
  return t;
}

