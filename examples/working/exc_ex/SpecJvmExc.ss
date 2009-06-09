class arith_exc extends __Exc {}
class runtime_exc extends __Exc{}


int testExc1() 
	requires true ensures res=0;
	{        
        int x = 0;
        try {
            if (x == 0) x = 1; else x = -1;
            if (x != 47) raise(new arith_exc());
            x = -1;
        } catch (arith_exc exc) {
            if (x == 1) x = 2; else x = -1;
        };
        if (x != 2) return -1;
        else return 0;
    }
    
int testExc2() 
	requires true ensures res = 0;
	{
        
        int x = 0;
        try {
            if (x == 0) x = 1; else x = -1;
            if (x != 47) raise(new runtime_exc());
            return -2;
        } catch (arith_exc exc) {
            x = -3;
			return -3;
        } catch (runtime_exc exc) {
            if (x == 1) x = 2; else x = -1;
        };
		if (x==-3) return -4;
        if (x == 2)
            return 0;
        else
            return -1;
    }
    
int testExc3() 
	requires true ensures res = 0;	
	{

        int x = 0;
        try {
            if (x == 0) x = 1; else x = -1;
            try {
                if (x != 1) x = -1; else x = 2;
                if (x != 47)
                    raise(new arith_exc ());
                else {
                    return -1;
                }
            } catch (arith_exc exc) {
                if (x != 2) x = -1; else x = 3;
            };
        } catch (arith_exc exc) {
            x = -1;
        };
        if (x == 3)
            return 0;
        else
            return -2;
    }
    
int testExc4() 
		requires true ensures res = 0;	
	{       
        int x = 0;
        try {
            if (x == 0) x = 1; else x = -1;
            try {
                if (x != 1) x = -1; else x = 2;
                if (x != 47) raise(new runtime_exc ());
            } catch (arith_exc exc) {
                x = -1;
            };
        } catch (runtime_exc exc) {
            if (x != 2) x = -1; else x = 3;
        };
        if (x == 3)
            return 0;
        else
            return -1;
    }
    
int testExc5() 
		requires true ensures res = 0;
	{
        int x = 0;
        try {
            if (x == 0) x = 1; else x = -1;
            try {
                if (x != 1) x = -1; else x = 2;
                if (x != 47) raise (new arith_exc ());
            } catch (arith_exc exc) {
                if (x != 2) x = -1; else x = 3;
                raise exc;
            };
        } catch (arith_exc exc) {
            if (x != 3) x = -1; else x = 4;
        };
        if (x == 4)
            return 0;
        else
            return -1;
    }
    
int throwArithmeticException(int a) throws arith_exc
	case {a=1 ->  requires true ensures res::arith_exc<> & flow arith_exc ;
		  a!=1 -> requires true ensures res=0;}
	{
        if (a == 1)
            raise(new arith_exc ());
        if (a == 1)
            return -1;
        else
            return 0;
    }
		
int dontDouble(int a) throws arith_exc
	case {a=1 ->  requires true ensures res::arith_exc<>& flow arith_exc ;
		  a!=1 -> requires true ensures res=a+a;}
	{
        throwArithmeticException(a);
        return a+a;
    }
		
		
int testExc6() 
		requires true ensures res = 0;
	{
        int x = 0;
        try {
            x = 1;
            throwArithmeticException(1);
            x = 2;
        } catch (arith_exc exc) {
            if (x != 1) x = -1; else x = 4;
        };
        if (x == 4)
            return 0;
        else
            return -1;
    }
    
int testExc7() 
		requires true ensures res = 0;
	{       
        int x = 0;
        try {
            x = 1;
            x = dontDouble(x);
            x = 2;
        } catch (arith_exc exc) {
            if (x != 1) x = -1; else x = 4;
        };
        if (x == 4)
            return 0;
        else
            return -1;
    }
    
int loopExitContinueInExceptionHandler() 
	requires true ensures res = 0;
	{        
        int i = 0;
        
		tr:while
			(i < 10000)
			case {i<9990 -> requires true ensures i'=9990& flow __Brk_top;
				  i>=9990 &	i<10000 -> requires true ensures i' = 10000;
				  i>=10000 -> requires true ensures i'=i;}
			{
            i++;
            try {
                if (i >9990)
                    raise(new arith_exc ());
                if (i == 9990)
                    break tr;
              
            } catch (arith_exc e) {
            };
        };
        if (i != 9990)
            return -2;
        return 0;
    }

