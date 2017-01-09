void main () {
  int x=1, y=4;
 { // [x->x14],  not yet (x,x14) 
   x = x+1;
   { 
     // [y->y1][x->x15][x->x14] not yet (y,y1),(x,x15),(x,14) 
     int x = x+y;
     // [y->y1][x->x15][x->x14] not yet (y,y1),(x,14) 
     int y = x;
     // [x->x15][x->x14] not yet (x,14) 
     x = x+y;
   }
   // [x->x14] not yet (x,x14)
   int x = x;
   // [x->x14] not yet 
   { 
     // [x->x16][x->x14] not yet (x,x16)
     int x = x;
     // [x->x16][x->x14] not yet 
     x = x+y;
   }
   // [x->x14] not yet 
   x=x+1;
 }
}

/*
# ex34b

rename_exp@1 EXIT:
{local: int x,int y
int x = 1, y = 4;
{local: int x_14
x = x + 1;
{local: int x_15,int y_16
int x_15 = x + y;
int y_16 = x_15;
x_15 = x_15 + y_16};
int x_14 = x;
 {local: int x_17
  int x_17 = x_14;
  x_17 = x_17 + y};
x_14 = x_14 + 1}}


*/
