
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
  infer [@term_wo_post]
 case {
   a=b -> ensures true;
   a=b+1 -> ensures true;
   a+1=b -> ensures true;
   a+1<b -> ensures true;
   a>b+1 -> ensures true;
  }
{

  if (x>0 || y>0) {
    //dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex30b.ss 

 case {
  x>0 | y>0 -> 
 case {
   a=b -> ensures true;
   a=b+1 -> ensures true;
   a+1=b -> ensures true;
   a+1<b -> ensures true;
   a>b+1 -> ensures true;
  }
  x<=0 & y<=0 -> 
   ensures true;
  }

# case-split is not so smart here as it seems
#  not to take previous case-split into account
# why so many requires false ensure false?

       y<=0 & x<=0 -> requires false & false
                      ensures false & false;



 case {
   (1<=x | 1<=y) -> 
   case {
     a=b -> 
     case {
       y<=0 & x<=0 -> requires false & false
                      ensures false & false;
                      
                        
       (((3+(2*a))<=((2*b)+y) & ((2*a)+x)<=(2+(2*b)) & (2+b)<=(a+x) & 
         (b+y)<=(1+a)) | 
        (x<=0 & 1<=y & (2+b)<=(a+x) & (b+y)<=(1+a)) | (a<=(b-2) & 1<=y) | 
        (y<=0 & (2+a)<=(b+y) & 1<=x) | 
        ((4+(3*a))<=((3*b)+y) & (b+y)<=(1+a) & (3+(2*b))<=((2*a)+x)) | 
        (a=b-1 & 1<=y) | (b<a & 1<=x) | 
        (x<=0 & (3+(2*b))<=((2*a)+x) & (2+a)<=(b+y))) -> 
       requires false & false
       ensures false & false;
       
         
       ((a<=(b-2) & (3+(2*b))<=(x+(2*a)) & (y+(3*b))<=(3+(3*a))) | 
        (b<=(a-2) & (x+(3*a))<=(3+(3*b)) & (3+(2*a))<=(y+(2*b))) | 
        ((3+(2*a))<=(y+(2*b)) & (x+(2*a))<=(2+(2*b)) & (4+(3*b))<=(x+(3*a)))) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) & (x+(2*a))<=(2+(2*b)) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (y+b)<=(1+a) & 1<=x & (a+x)<=(1+b) -> 
       requires false & false
       ensures false & false;
       
         
       b=a+1 & y<=0 & 1<=x -> requires false & false
                              ensures false & false;
                              
                                
       b=a-1 & x<=0 & 1<=y -> requires false & false
                              ensures false & false;
                              
                                
       b=a & x<=0 & 1<=y -> 
       requires emp & Term[64,4,0+(0*x)+(1*y)+(0*a)+(0*b)]
       ensures true & ((0<x | 0<y)) & a=b;
       
         
       b=a & y<=0 & 1<=x -> 
       requires emp & Term[64,5,0+(1*x)+(0*y)+(0*a)+(0*b)]
       ensures true & ((0<x | 0<y)) & a=b;
       
         
       b=a & 1<=y & 1<=x -> 
       requires emp & Term[64,6,0+(1*x)+(0*y)+(0*a)+(0*b)]
       ensures true & ((0<x | 0<y)) & a=b;
       
         
       b<=(a-2) & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a)) -> 
       requires false & false
       ensures false & false;
       
         
       b<=(a-2) & (x+a)<=(1+b) & 1<=y & (b+y)<=(1+a) -> 
       requires false & false
       ensures false & false;
       
         
       }
       
     a=1+b -> 
     case {
       y<=0 & x<=0 -> requires false & false
                      ensures false & false;
                      
                        
       (((3+(2*a))<=((2*b)+y) & ((2*a)+x)<=(2+(2*b)) & (2+b)<=(a+x) & 
         (b+y)<=(1+a)) | 
        (x<=0 & 1<=y & (2+b)<=(a+x) & (b+y)<=(1+a)) | (a<=(b-2) & 1<=y) | 
        (y<=0 & (2+a)<=(b+y) & 1<=x) | 
        ((4+(3*a))<=((3*b)+y) & (b+y)<=(1+a) & (3+(2*b))<=((2*a)+x)) | 
        (a=b-1 & 1<=y) | (b<a & 1<=x) | 
        (x<=0 & (3+(2*b))<=((2*a)+x) & (2+a)<=(b+y))) -> 
       requires emp & Loop{call 24:4}[]
       ensures false & false;
       
         
       ((a<=(b-2) & (3+(2*b))<=(x+(2*a)) & (y+(3*b))<=(3+(3*a))) | 
        (b<=(a-2) & (x+(3*a))<=(3+(3*b)) & (3+(2*a))<=(y+(2*b))) | 
        ((3+(2*a))<=(y+(2*b)) & (x+(2*a))<=(2+(2*b)) & (4+(3*b))<=(x+(3*a)))) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) & (x+(2*a))<=(2+(2*b)) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (y+b)<=(1+a) & 1<=x & (a+x)<=(1+b) -> 
       requires false & false
       ensures false & false;
       
         
       b=a+1 & y<=0 & 1<=x -> requires false & false
                              ensures false & false;
                              
                                
       b=a-1 & x<=0 & 1<=y -> 
       requires emp & Term[64,3,0+(0*x)+(1*y)+(0*a)+(0*b)]
       ensures true & ((0<x | 0<y)) & a=1+b;
       
         
       b=a & x<=0 & 1<=y -> requires false & false
                            ensures false & false;
                            
                              
       b=a & y<=0 & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b=a & 1<=y & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b<=(a-2) & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a)) -> 
       requires false & false
       ensures false & false;
       
         
       b<=(a-2) & (x+a)<=(1+b) & 1<=y & (b+y)<=(1+a) -> 
       requires false & false
       ensures false & false;
       
         
       }
       
     1+a=b -> 
     case {
       y<=0 & x<=0 -> requires false & false
                      ensures false & false;
                      
                        
       (((3+(2*a))<=((2*b)+y) & ((2*a)+x)<=(2+(2*b)) & (2+b)<=(a+x) & 
         (b+y)<=(1+a)) | 
        (x<=0 & 1<=y & (2+b)<=(a+x) & (b+y)<=(1+a)) | (a<=(b-2) & 1<=y) | 
        (y<=0 & (2+a)<=(b+y) & 1<=x) | 
        ((4+(3*a))<=((3*b)+y) & (b+y)<=(1+a) & (3+(2*b))<=((2*a)+x)) | 
        (a=b-1 & 1<=y) | (b<a & 1<=x) | 
        (x<=0 & (3+(2*b))<=((2*a)+x) & (2+a)<=(b+y))) -> 
       requires emp & Loop{call 24:4}[]
       ensures false & false;
       
         
       ((a<=(b-2) & (3+(2*b))<=(x+(2*a)) & (y+(3*b))<=(3+(3*a))) | 
        (b<=(a-2) & (x+(3*a))<=(3+(3*b)) & (3+(2*a))<=(y+(2*b))) | 
        ((3+(2*a))<=(y+(2*b)) & (x+(2*a))<=(2+(2*b)) & (4+(3*b))<=(x+(3*a)))) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) & (x+(2*a))<=(2+(2*b)) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (y+b)<=(1+a) & 1<=x & (a+x)<=(1+b) -> 
       requires false & false
       ensures false & false;
       
         
       b=a+1 & y<=0 & 1<=x -> 
       requires emp & Term[64,2,-3+(2*x)+(0*y)+(3*a)+(-3*b)]
       ensures true & ((0<x | 0<y)) & 1+a=b;
       
         
       b=a-1 & x<=0 & 1<=y -> requires false & false
                              ensures false & false;
                              
                                
       b=a & x<=0 & 1<=y -> requires false & false
                            ensures false & false;
                            
                              
       b=a & y<=0 & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b=a & 1<=y & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b<=(a-2) & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a)) -> 
       requires false & false
       ensures false & false;
       
         
       b<=(a-2) & (x+a)<=(1+b) & 1<=y & (b+y)<=(1+a) -> 
       requires false & false
       ensures false & false;
       
         
       }
       
     (1+a)<b -> 
     case {
       y<=0 & x<=0 -> requires false & false
                      ensures false & false;
                      
                        
       (((3+(2*a))<=((2*b)+y) & ((2*a)+x)<=(2+(2*b)) & (2+b)<=(a+x) & 
         (b+y)<=(1+a)) | 
        (x<=0 & 1<=y & (2+b)<=(a+x) & (b+y)<=(1+a)) | (a<=(b-2) & 1<=y) | 
        (y<=0 & (2+a)<=(b+y) & 1<=x) | 
        ((4+(3*a))<=((3*b)+y) & (b+y)<=(1+a) & (3+(2*b))<=((2*a)+x)) | 
        (a=b-1 & 1<=y) | (b<a & 1<=x) | 
        (x<=0 & (3+(2*b))<=((2*a)+x) & (2+a)<=(b+y))) -> 
       requires emp & Loop{call 24:4}[]
       ensures false & false;
       
         
       ((a<=(b-2) & (3+(2*b))<=(x+(2*a)) & (y+(3*b))<=(3+(3*a))) | 
        (b<=(a-2) & (x+(3*a))<=(3+(3*b)) & (3+(2*a))<=(y+(2*b))) | 
        ((3+(2*a))<=(y+(2*b)) & (x+(2*a))<=(2+(2*b)) & (4+(3*b))<=(x+(3*a)))) -> 
       requires emp & MayLoop[]
       ensures true & ((0<x | 0<y)) & (1+a)<b;
       
         
       a<=(b-2) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) & (x+(2*a))<=(2+(2*b)) -> 
       requires emp & Term[64,9]
       ensures true & ((0<x | 0<y)) & (1+a)<b;
       
         
       a<=(b-2) & (y+b)<=(1+a) & 1<=x & (a+x)<=(1+b) -> 
       requires emp & Term[64,7]
       ensures true & ((0<x | 0<y)) & (1+a)<b;
       
         
       b=a+1 & y<=0 & 1<=x -> requires false & false
                              ensures false & false;
                              
                                
       b=a-1 & x<=0 & 1<=y -> requires false & false
                              ensures false & false;
                              
                                
       b=a & x<=0 & 1<=y -> requires false & false
                            ensures false & false;
                            
                              
       b=a & y<=0 & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b=a & 1<=y & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b<=(a-2) & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a)) -> 
       requires false & false
       ensures false & false;
       
         
       b<=(a-2) & (x+a)<=(1+b) & 1<=y & (b+y)<=(1+a) -> 
       requires false & false
       ensures false & false;
       
         
       }
       
     (1+b)<a -> 
     case {
       y<=0 & x<=0 -> requires false & false
                      ensures false & false;
                      
                        
       (((3+(2*a))<=((2*b)+y) & ((2*a)+x)<=(2+(2*b)) & (2+b)<=(a+x) & 
         (b+y)<=(1+a)) | 
        (x<=0 & 1<=y & (2+b)<=(a+x) & (b+y)<=(1+a)) | (a<=(b-2) & 1<=y) | 
        (y<=0 & (2+a)<=(b+y) & 1<=x) | 
        ((4+(3*a))<=((3*b)+y) & (b+y)<=(1+a) & (3+(2*b))<=((2*a)+x)) | 
        (a=b-1 & 1<=y) | (b<a & 1<=x) | 
        (x<=0 & (3+(2*b))<=((2*a)+x) & (2+a)<=(b+y))) -> 
       requires emp & Loop{call 24:4}[]
       ensures false & false;
       
         
       ((a<=(b-2) & (3+(2*b))<=(x+(2*a)) & (y+(3*b))<=(3+(3*a))) | 
        (b<=(a-2) & (x+(3*a))<=(3+(3*b)) & (3+(2*a))<=(y+(2*b))) | 
        ((3+(2*a))<=(y+(2*b)) & (x+(2*a))<=(2+(2*b)) & (4+(3*b))<=(x+(3*a)))) -> 
       requires emp & MayLoop[]
       ensures true & ((0<x | 0<y)) & (1+b)<a;
       
         
       a<=(b-2) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) & (x+(2*a))<=(2+(2*b)) -> 
       requires false & false
       ensures false & false;
       
         
       a<=(b-2) & (y+b)<=(1+a) & 1<=x & (a+x)<=(1+b) -> 
       requires false & false
       ensures false & false;
       
         
       b=a+1 & y<=0 & 1<=x -> requires false & false
                              ensures false & false;
                              
                                
       b=a-1 & x<=0 & 1<=y -> requires false & false
                              ensures false & false;
                              
                                
       b=a & x<=0 & 1<=y -> requires false & false
                            ensures false & false;
                            
                              
       b=a & y<=0 & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b=a & 1<=y & 1<=x -> requires false & false
                            ensures false & false;
                            
                              
       b<=(a-2) & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a)) -> 
       requires emp & Term[64,10]
       ensures true & ((0<x | 0<y)) & (1+b)<a;
       
         
       b<=(a-2) & (x+a)<=(1+b) & 1<=y & (b+y)<=(1+a) -> 
       requires emp & Term[64,8]
       ensures true & ((0<x | 0<y)) & (1+b)<a;
       
         
       }
       
     }
     
   x<=0 & y<=0 -> requires emp & Term[64,1]
                  ensures true & y<=0 & x<=0;
                  
                    


*/
