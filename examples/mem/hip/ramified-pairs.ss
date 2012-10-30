data pair {
	int fst; 
	int snd;
}

void mark(pair p, pair q)
  requires p::pair<vpf,vps> & q::pair<vqf,vqs> & vpf != 1 & vqf != 1 & vps != 1 & vqs != 1
  ensures p::pair<1,1> & q::pair<1,1> ;
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
