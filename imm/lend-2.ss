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
 requires p::pair<f,_>
 ensures p::pair<f,f>;
 requires p::pair<v@L,_@M>
 ensures p::pair<_@A,v@M>;
{
 p.snd=p.fst;
}

int wrong(pair p)
/*
 requires p::pair<v,_>@L
 ensures p::pair<v,_>@L & es=v;
*/
 requires p::pair<v@L,_@A>
  ensures p::pair<v@L,_@A> &res=v;
// above failed only under --field-ann
{
 return p.fst;
}

int main(pair p)
 requires p::pair<v,a>
 ensures p::pair<v,a> & res=v;

{
  //  int t = wrong(p);
  int t = first(p);
  //dprint;
  return t;
}

