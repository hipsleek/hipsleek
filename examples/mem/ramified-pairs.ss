data pair {
	int fst; 
	int snd;
}

void mark(pair p)
requires p::pair<f,_@A> & p::pair<_@A,s> & !(f = 1 & s = 0) & 0<=f<=1 & 0<=s<=1
ensures p::pair<1,1>;
{
if(p.fst == 1){
	return;}
else {
	if (p.snd == 1){
		p.fst = 1;
		return;}
	else {
	p.snd = 1;
	p.fst = 1;}
	}
return;
}
