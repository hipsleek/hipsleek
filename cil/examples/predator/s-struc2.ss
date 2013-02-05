
data item_t {
  int val;
  item_t next;
}

pointer_type_1 cast_pointer_type_0_to_pointer_type_1(pointer_type_0 param)
  case { 
    param =  null -> requires true ensures res = null; 
    param != null -> requires true ensures res::pointer_type_1<_>; 
  }


int foo1 ()
   requires true
   ensures res > 0;
{
  item_t node = new item_t(1,null);
  return node.val;
}

item_t foo2 ()
   requires true
   ensures res != null;
{
  item_t node1 = new item_t(1,null);
  item_t node2 = new item_t(1,node1);
  return node2.next;
}

