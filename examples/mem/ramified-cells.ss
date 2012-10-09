data cell {
	int val; 
}

void mark(cell p, cell q)
	requires p::cell<vp> && q::cell<vq> & !(vp = 1 & vq = 0) & 0<=vp<=1 & 0<=vq<=1
	ensures p::cell<1> && q::cell<1>;
{
if(p.val == 1){
	return;}
else {
	if (q.val == 1){
		p.val = 1;
		return;}
	else {
	q.val = 1;
	p.val = 1;}
	}
return;
}
