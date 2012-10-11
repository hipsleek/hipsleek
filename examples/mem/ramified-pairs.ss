data pair {
	int fst; 
	int snd;
}
data cell{
  int v;
}

pred order(f,s,flag) ==
     f::cell<1> /\ s::cell<1> & flag
  or f::cell<v> /\ s::cell<_> & v!=1 & !flag

void mark(pair p)
  requires p::pair<f,s> * order(f,s,_)
  ensures p::pair<f,s> * order(f,s,true);
{
if(p.fst.v == 1){
    //f::cell<1> /\ s::cell<1> 
	return;}
else {
	if (p.snd.v == 1){
        //f::cell<v> /\ s::cell<1> & v!=1
		p.fst.v = 1;
        //f::cell<1> /\ s::cell<1> & v!=1 
		return;}
	else {
    // f::cell<v> /\ s::cell<r> & v!=1 & r!=1 
	p.snd.v = 1;
    // f::cell<_> /\ s::cell<1> & v!=1 & r!=1 
	p.fst.v = 1;}
    // f::cell<1> /\ s::cell<1> & v!=1 & r!=1 
	}
return;
}
