data cell {
	int val; 
}


void ex0(ref cell f, ref cell s)
  requires f::cell<v> U* s::cell<r> & v != 1 & r != 1 & (v = r | v != r)
  ensures f'::cell<v> U* s'::cell<1> & v != 1; 
  requires f::cell<v> & s::cell<r> & v != 1  & r != 1
  ensures f'::cell<_> U* s'::cell<_>; 
{
	cell m = new cell(1);
	s = m;
	//assert(f = s);
}

void ex1(cell f, cell s)
  requires f::cell<v> U* s::cell<r> & v != 1 & r != 1
  ensures f::cell<_> U* s::cell<1>; 
{
	s.val = 1;
}


void mark(cell f, cell s)
  requires f::cell<v> U* s::cell<r> & v != 1 & r != 1
  ensures  f::cell<1> U* s::cell<1>;
{
if(f.val == 1){
     //f::cell<1> /\ s::cell<1> 
	return;}
else {
	if (s.val == 1){
        //f::cell<v> /\ s::cell<1> & v!=1
		f.val = 1;
        //f::cell<1> /\ s::cell<1> & v!=1 
		return;}
	else {
    // f::cell<v> /\ s::cell<r> & v!=1 & r!=1 
	s.val = 1;
    // f::cell<_> /\ s::cell<1> & v!=1 & r!=1 
	f.val = 1;}
    // f::cell<1> /\ s::cell<1> & v!=1 & r!=1 	
}
return;
}
