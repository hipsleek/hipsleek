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
     x = x+1;
   }
   // [x->x14] not yet 
   x=x+1;
 }
}

/*
# ex34b

renaming incorrect..

ERROR: at ex34b-rename-loop.ss_4:11_4:12
Message: x_14, line 4, col 11 is used before declared

int x = 1;
{local: int x_14
x_14 = x_14 + 1;
{local: int x_15
int x_15 = x_15;
x_15 = x_15 + 1};
int x_14 = x_14;
x_14 = x_14 + 1}}



*/
