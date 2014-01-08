data pair {
	int fst; 
	int snd;
}

int sum(pair p, pair q)
  requires p::pair<f1@I,_@A> & q::pair<f2@I,_@A>
  ensures p::pair<f1@I,_@A> & p = q & res = f1 + f2;
{
return p.fst + q.fst;
}
