data pair {
	int fst; 
	int snd;
}

void mark(pair p, pair q)
  requires p::pair<f,s> & q::pair<0,0> & f != 1 & s !=1
  ensures p::pair<1,1> & q::pair<_,_>;
{
if(p.fst == 1){
	return;}
else {
	if (p.snd == 1){
		p.fst = 1;
		return;}
	else {
	p.snd = 1;
	//dprint;
	p.fst = 1;}
	}
return;
}
