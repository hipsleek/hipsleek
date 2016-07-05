data pair{
 int fst;
 int snd;
}

int first(pair p)
/*
 requires p::pair<v,_>@L
 ensures res=v;
*/
 requires p::pair<v@L,_@A>
 ensures res=v;
{
 return p.fst;
}

void trf(pair p)
/*
 requires p::pair<f,_>
 ensures p::pair<f,f>;
*/
 requires p::pair<v@L,_@M>
 ensures p::pair<_@A,v@M>;
{
 p.snd=p.fst;
}


int main(pair p)
 requires p::pair<v,_>
 ensures p::pair<v,res> & res=v;
{
  trf(p);
  return p.snd;
}

int main2(pair p)
 requires p::pair<v,a>
 ensures p::pair<v,a> & res=v;
{
  int t=first(p);
  return t;
}
