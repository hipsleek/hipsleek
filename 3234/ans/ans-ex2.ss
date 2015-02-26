data cell {int val;}

void swap (cell i, cell j)
  requires i::cell<a> & i=j
  ensures  i::cell<a>;
  requires i::cell<a>*j::cell<b>
  ensures  i::cell<b>*j::cell<a>;
{
	int c=i.val;
	i.val = j.val;
	j.val = c;	
}
