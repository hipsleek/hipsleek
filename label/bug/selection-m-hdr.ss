/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<"n":n, "v":sm, "v":bg, "v":mi> == 
	self::node<mi, null> & ["n":n=1; "v":sm <= mi < bg] or
	self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & ["n":n1=n-1; "v":sm <= d < bg & mi = min(d, tmi)]
  //  inv self!=null & ["n":n>=1; "v":sm<=mi<bg];

  inv self!=null & (( AndList("n":n >= 2; "v":sm <= mi < bg))
                    | ((AndList ("n":n = 1; "v":sm <= mi < bg))));

  /* inv self!=null & ((n >= 2 & sm <= mi < bg) */
  /*                   | (n = 1 & sm <= mi < bg)); */

  /* inv AndList("":self!=null; "n":n >= 2; "v":sm <= mi < bg) */
  /*    | AndList ("":self!=null; "n":n = 1; "v":sm <= mi < bg); */


/*
sll<"n":n, "v":sm, "v":lg> == 
	self::node<sm, null> & ["n":n=1; "v":sm = lg] or 
        self::node<sm, q> * q::sll<n1, qs, lg> & q != null & ["n":n1=n-1; "v":sm <= qs]
        inv true & ["n":n >= 1; "v":sm <= lg]; 
*/











