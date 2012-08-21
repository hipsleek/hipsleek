

data cell{
  int val;
}
 
//view definitions

//cell_v<n> == self::cell<n>;
//endpoint_v<c, s, r> == self::endpoint<c,s,r>;


// message definitions

message packet <> == true  ;
message packet_one <cell x3> == x3::cell<_>  ;
message packet_two <cell x1,cell x2> == x1::cell<n1> * x2::cell<n2> & n=44  ;
message packet_test <> == true  ;
 
 


//message start [emp]
 
//contract definitions

contract C { 
  initial  state start { ?packet_two -> middle;  
			 ?packet_one -> end1;
			  } 

  state middle {!packet_one -> next;}

  state next {!packet_one -> end1; 
	      !packet -> end2;
	      !packet_two -> end3;
	     } 
 
  state end1 {}
  state end2 {}
  state end3 {}

}

 


void get(endpoint f) 
    requires f::endpoint <C, 2, 1>
   ensures f::endpoint <C, st, 1> & (st = 4 |  st = 5 | st = 6 );
 {
  cell x, y;
  int n;

 receive(packet_one,f,x);
  
  switch_receive {    
    receive(packet_one,f, x) : {n = 1; }
    receive(packet, f): {n=3;}
    receive(packet_two,f, x, y) : {n = 2;}
  };
  dprint;
} 
 


 



