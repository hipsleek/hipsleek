data cell {
	int val; 
}

pred order(f,s,flag) ==
     f::cell<1> /\ s::cell<1> & flag
  or f::cell<v> /\ s::cell<_> & v!=1 & !flag

void mark(cell p, cell q)
  requires order(f,s,_)
  ensures  order(f,s,true);
{
if(p.val == 1){
     f::cell<1> /\ s::cell<1> 
	return;}
else {
	if (q.val == 1){
        //f::cell<v> /\ s::cell<1> & v!=1
		p.val = 1;
        //f::cell<1> /\ s::cell<1> & v!=1 
		return;}
	else {
    // f::cell<v> /\ s::cell<r> & v!=1 & r!=1 
	q.val = 1;
    // f::cell<_> /\ s::cell<1> & v!=1 & r!=1 
	p.val = 1;}
    // f::cell<1> /\ s::cell<1> & v!=1 & r!=1 	
}
return;
}

/*
Ramified Assignment
f::cell<v> /\ s::cell<r> & v != 1 & r != 1
	s.val = 1;
(s::cell<r> --* f::cell<v> /\ s::cell<r>) * s::cell<1> & v != 1 & r != 1
	f.val = 1;
f::cell<v> --* ((s::cell<r> --* f::cell<v> /\ s::cell<r>) * s::cell<1>) * f::cell<1> & v != 1 & r != 1 
|- f::cell<1> /\ s::cell<1>

After Matching Nodes

f::cell<v> --* (s::cell<r> --* f::cell<v> /\ s::cell<r>)

XPure = ({f} U {s} - {s}) - {f} = {}

treating --* as set difference
*/
