void inc(ref int* p)
  requires p::int_ptr<v>
  ensures p::int_ptr<v+1> & p'=p; //'
{
   (*p) = (*p) + 1;
}

void main()
  requires true
  ensures true;
{ int x,y,z;
   x= 7;
   y=8;
   if (true){
     int* ptr;
     ptr=&x;
     inc(ptr);
     int t = 9;
     ptr=&t;
     //expecting delete(t) here
   }else{
     int* ptr2 = &y;
     inc(ptr2);
     int t = 9;
     ptr2=&t;
     //expecting delete(t) here
   }
   int z1 = x;
   assert(z1'=8);
   int z2 = y;
   assert(z2'=8);
}
