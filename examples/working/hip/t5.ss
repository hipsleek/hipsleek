class e1 extends __Exc {}

class e3 extends __Exc {}

class e2 extends e1    {}
class e4 extends e1    {}
class e5 extends e1    {}

data node{int i; node n;}

void m0 (ref int i, e4 z) throws e1
	requires z::e4<>
	ensures i>0 & i'=2 or
		i<=0 & i'=3;
{
	try{
		if (i>0) raise z; // new e1();
		//dprint;
                else i=3;
		//dprint;
	}catch (e1 v){
		i=2;
		//dprint;
		//assert false;
		//raise new e4();
	};
        //dprint;
	
}

// problem e1 -> e2 after catching!
// w

void m1 (ref int i, e1 z) throws e4,e1
	requires z::e1<>
	//ensures i'=3 or eres::e1<> & i>0;
	ensures //res::e5<> & i'=2 & flow e1 or 
		res::e4<> & i>0 & i'=3 & flow e4 or
		res::e1<> & i>0 & flow e1 or  
		i<=0 & i'=-3;
/*
static  z::<> & true & {FLOW,(25,26)=__norm,}
   EAssume (5, ):ref [i]
     res::<> & 0<i & i'=3 & {FLOW,(31,32)=e4,} // err res::?
     or res::<> & 0<i & {FLOW,(29,34)=e1,}
     or true & i<=0 & i'+3=0 & {FLOW,(25,26)=__norm,}

data e5 {
}   // extends not displayed

*/
{
	try{
		if (i>0) raise z; // new e1();
		//dprint;
	}catch (e2 v){
        // dprint;
		i=4;
		//dprint;
		//assert false;
		//raise v;
		raise new e4();
	};
	i=-3;
        dprint;
}

 void nonnull(node x)
   case {
    x=null -> ensures true & flow e1;
     x!=null -> requires x::node<a,b>
       ensures x::node<a,b>;
   }

void m1a (ref int i, e1 z) throws e1
	requires z::e1<>
	//ensures i'=3 or eres::e1<> & i>0;
	ensures //res::e5<> & i'=2 & flow e1 or 
        res::e2<> & i>0 & i'=4 & flow e2 or  
		res::e1<> & i>0 & i'=1 & flow e1 or
		i<=0 & i'=-3;
{
	try{
      if (i>0) {i=1; raise z;}; // new e1();
		//dprint;
	}catch (e2 v){
        // dprint;
		i=4;
		//dprint;
		//assert false;
		raise v;
// state:es_formula: (137, ):z::e1<> & z' = z & (134, ):0 < i & (135, ):v_bool_64_242' & v_e1_64_241' = z' 
// & v_46' = v_e1_64_241' & i' = 4 & v_e2_71_239' = v_46' & res = v_e2_71_239'&{FLOW,(33,34)=e2,}
// cannot prove: res::e2<> & i>0 & i'=4 & flow e2
// good if we can refine res to becomde e2 
// type error for: res::e2<> & i>0 & i'=4 & flow e1
//   -> ok now; change to checking for overlap instead
	};
	i=-3;
        dprint;
}

void m2 (ref int i) throws e1
	requires true
	//ensures i'=3 or eres::e1<> & i>0;
	//ensures eres::e4<>&i'=2;
	//ensures i<=0 & i'=3;
	ensures res::e4<>  & flow e4 // error - cannot prove i'=2
               or i<=0 & i'=3 ;
{
	//dprint;
	try{
		if (i>0) raise new e1();
	}catch (e1 v){
		i=2;
		/*raise new node(1,null);*/
		raise new e4();
	};
		/*
			try{
			} catch (e2 v) {
				// dead code
				assert false;
				i=4;
				raise new e5();
			};
		*/
	i=3;
        dprint;
}




void m(ref int i)
requires i>0 
ensures i'=i+3;
{
	i=i+1;
        dprint;
	i=i+2;
	dprint;
}

