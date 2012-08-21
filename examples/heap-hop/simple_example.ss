 data cell{
  int val;
}
 
// message definitions

message packet <> == true  ;
message packet_one <cell x3> == x3::cell<m> & m=44 ;
message packet_two <cell x1,cell x2> == x1::cell<n1> * x2::cell<_> & n1=55  ;


//contract definitions

contract C { 
  initial  state start { !packet_one -> end;
			  } 
 
  state next {!packet_one -> end; }
 
  final state end {}

}



void put_get() 
  requires true
  ensures true;
{
  endpoint e,f;
  cell x;  
  x = new cell(44);
  
  open(C, e, f);
 
  int t = fork(put, e, x);
  get(f);
  
  join(t); 
  close(e,f);
 
}

  
void get(endpoint f) 
  requires f::endpoint <C, 1, 1>
  ensures f::endpoint <C, 3, 1>;
 
 {
  cell x, y; 
  receive(packet_one,f, y);  
} 

void put(endpoint e, cell c) 
  requires e::endpoint<C, 1, 0> * c::cell<n> & n=44 
  ensures e::endpoint<C, 3, 0>;  
{ 
   send(packet_one, e, c);  
} 


 