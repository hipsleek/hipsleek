data item {
 item next
}

ls<p,n> == self = p & n=0
  or self::item<q> * q::ls<p,m> & n=m+1
  inv n>=0;

void create()
	requires true
	ensures true;
{
	item ptr;

	ptr = null;
	loop(ptr);
	return;
}

void loop(ref item ptr)
      requires ptr::ls<null,n>
      ensures ptr'::ls<null,m> & m>=n; //' 
{
		item data1 = ptr;
		ptr = malloc();
		if (ptr==null) {
		  ptr = data1;
		  break; //return;
                }
		ptr.next = data1;
		loop(ptr);
}

item malloc ()
 requires true
 ensures res=null or res::item<null>;

