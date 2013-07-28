data node {
 int mark;
 node left;
 node right;
}

tx<g,s,"s":M> == true&["":self = g & s!=null & (g=null | g=s) ; "s": M={}]
   or self::node<v,l,r> * l::tx<g,s,M1> * r::tx<null,s,M2> & ["": self != g & self != s ;"s": M=union({v},M1,M2)]
   or self::node<v,l,r> * l::tx<null,s,M1> * r::tx<g,s,M2> & ["": self != g & self != s ;"s": M=union({v},M1,M2)]
inv true&["": s!=null & (g=null & self!=s | g=s & self!=null); 
    "s":(self=g & M={} | self!=g & M!={})];


void lscan(ref node cur, ref node prev, node sent)
/*
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=null & b=sent 
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a & a=sent & b=null
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 


requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> & cur != a &
        (a=null & b=sent | a=sent & b=null)
ensures prev'::tx<null,sent,union(M1,M2)>  & cur' = sent & prev'!=null; 
*/
requires cur::tx<a,sent,M1> * prev::tx<b,sent,M2> 
 case { 
    a=null ->
       case { 
         b=sent & cur!=null ->
            ensures prev'::tx<null,sent,M3>  & ["": cur' = sent 
            & prev'!=null
            ; "s": M3=union(M1,M2)]; 
         b!=sent | cur=null -> 
            requires false
            ensures false;
        }
    a!=null ->
       case { 
         b=null & cur!=sent & a=sent ->
             ensures prev'::tx<null,sent,M3>  & ["": cur' = sent 
             & prev'!=null 
             ;"s": M3=union(M1,M2)];
         b!=null | cur=sent | a!=sent -> 
            requires false
            ensures false;
        }
  }

{

  node n,tmp;
  n = cur.left;
  tmp = cur.right;
  // rotate ptrs
  cur.right = prev;
  cur.left = tmp;
  // move forward
  prev = cur;
  cur = n;
  if (cur == sent) {
        return;
  }
  if (cur == null) {
      //assume false;
      // change direction;
      cur = prev;
      prev = null;
  }
  lscan(cur,prev,sent);
}

/*
Procedure lscan$node~node~node SUCCESS
Stop Omega... 378 invocations 
!!! Logging logs/no_eps_proof_log_swt-4g-set-lbl_ss.txt

!!! Number of log entries 6627
!!! Logging logs/sleek_log_swt-4g-set-lbl_ss.txt

2 false contexts at: ( (57,8)  (56,19) )

!!! time_log (small):(133.909343,6785)
!!! log (>.5s)():(213.773794,[1.470697,1.143503,0.712045,0.712045,1.370331,2.040128,1.170563,0.7881,1.283992,0.985438,0.688043,0.688043,1.376437,2.028126,1.161275,0.717808,1.555186,1.498842,1.273214,0.512032,1.120069,1.120069,1.692391,0.708044,0.716045,2.440152,3.020189,1.353818,4.086345,0.668041,1.601475,1.327203,1.242945,1.032065,1.036065,1.68171,0.704044,0.712045,2.348147,2.888181,1.431721,4.035508,0.608038,0.592876,0.761274,1.104694,1.118434,0.59706,0.755523,1.108531,1.104237,2.642296,1.795031,0.596178,0.767229,1.146399,1.144727,0.604157,0.900653,1.152416,1.145975,2.660531,1.732296,2.692461,2.086287,2.71454,2.065274,1.695797,2.721809,2.102427,2.718646,2.079701,1.148796,1.139797,0.716045,0.720045,1.629385,2.07213,1.110515,0.566895,1.62767,0.904565,1.324168,0.504032,1.136072,1.144072,0.724045,0.724045,2.184137,2.788174,1.952261,4.959691,0.676042,1.302697,1.358157,1.763983,0.532033,1.152072,1.152072,0.720045,0.720045,1.396517,2.492156,3.072192,1.886565,3.712646,0.668042,1.449033,1.092439,0.672043,0.672043,1.480092,0.762528,1.100679,1.28008,1.238222,1.589476,2.129859,1.115116,0.60421,0.769906,1.076243,1.06293,2.655738,1.300455,3.225919,2.228181,3.29081,2.261169,3.155523,2.119638,3.149268,2.12326,1.204076,1.220077,3.253907,2.227665,3.229586,2.294202])
!!! log (>.5s)():(213.773794,[10.,10.,10.,10.,10.,10.,10.,5.,10.,5.,10.,10.,10.,10.,10.,10.,10.,5.,10.,5.,10.,5.])
Total verification time: 403.169194 second(s)
	Time spent in main process: 40.154508 second(s)
	Time spent in child processes: 363.014686 second(s)
	Time for logging: 25.453608 second(s)
*/