data ptr_item {
 item val
}

data item {
 item next
}

 x::ptr_item<v>*v::item<_>


ls<> == self = null
	or self::item<q> * q::ls<> 
  inv true;

void create()
	requires true
	ensures true;
{
	item ptr;

	ptr = null;
	while (true)
          requires ptr::ls<>
	  ensures ptr'::ls<>; //'
        {
		item data1 = ptr;
		ptr = malloc();
		if (ptr==null) break;
		ptr.next = data1;
	}
	return;
}

item malloc ()
 requires true
 ensures res=null or res::item<null>;

