global int* p;

void inc(ref int* p)
  requires p::int_ptr<v>
  ensures p::int_ptr<v+1> & p'=p; //'
{
   (*p) = (*p) + 1;
}

void main()
  requires true
  ensures true;
{ int x,y;
   x= 7;
   p =&x;
   inc(p);
   while(true)
     requires true
     ensures true;
   {
     int z=5;
     int* ptr2 = &z;
     z = z +1;
     //expecting delete(z) after translation
   }
   int z = x;
   assert(z'=8);
}
