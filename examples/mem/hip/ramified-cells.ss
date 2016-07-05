data cell {
	int val; 
}

void ex0(ref cell f, ref cell s)
  requires f::cell<v> & s::cell<r> & v != 1 & r != 1 & (v = r | v != r)
  ensures f'::cell<v> & s'::cell<1> & v != 1; 
  requires f::cell<v> && s::cell<r> & v != 1  & r != 1
  ensures f'::cell<_> & s'::cell<_>; 
{
	cell m = new cell(1);
	s = m;
	//assert(f = s);
}

void ex1(cell f, cell s)
  requires f::cell<v> & s::cell<r> & v != 1 & r != 1
  ensures f::cell<_> & s::cell<1>; 
{
	s.val = 1;
}


void mark(cell f, cell s)
  requires f::cell<v> & s::cell<r> & v != 1 & r != 1
  ensures  f::cell<1> & s::cell<1>;
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

cell ex3(ref cell a1, ref cell a2)
requires a1::cell<_> & a2::cell<_>
ensures res::cell<7>;
{
cell t1 = a1;
t1.val = 7;
cell t2 = a2;
t2.val = 8;
cell t3 = a1;
cell t4 = t3;
dprint;
return t4;
}

cell ex4(ref cell a1, ref cell a2)
requires a1::cell<_> * a2::cell<_>
ensures res::cell<7>;
{
cell t1 = a1;
t1.val = 7;
cell t2 = a2;
t2.val = 8;
cell t3 = a1;
cell t4 = t3;
dprint;
return t4;
}
