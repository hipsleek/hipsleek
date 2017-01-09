public class Infix2Postfix {
    public static LinkedList buildExpression(int n) {
	LinkedList exp = null;
	for (int i = 1; i <= n; i++) {
	    if (i <= n-1) exp = new LinkedList(')', exp);
	    exp = new LinkedList(')', exp);
	    exp = new LinkedList('b', exp);
	    exp = new LinkedList('+', exp);
	    exp = new LinkedList('a', exp);
	    exp = new LinkedList('(', exp);
	    if (i <= n-1) exp = new LinkedList('*', exp);
	}

	for (int i = 1; i < n; i++)
	    exp = new LinkedList('(', exp);

	return exp;
    }

    public static LinkedList toPostfix(LinkedList infix) {
	LinkedList operators = null, operands = null;
	while (infix != null) {
	    char c = infix.getFirst();
	    switch (c) {
	    case '(': break;
	    case '+': case '-': case '*': case '/':
		operators = new LinkedList(c, operators);
		break;
	    case ')':
		operands = new LinkedList(operators.getFirst(), operands);
		operators = operators.getTail();
		break;
	    default:
		operands = new LinkedList(c, operands);
	    }
	    infix = infix.getTail();
	}

	LinkedList postfix = null;
	while (operands != null) {
	    postfix = new LinkedList(operands.getFirst(), postfix);
	    operands = operands.getTail();
	}

	return postfix;
    }

    public static void  main(String args[]) {
	LinkedList infix = buildExpression(args.length);
	// System.out.println("infix = " + infix);
	LinkedList postfix = toPostfix(infix);
	// System.out.println("postfix = " + postfix);
    }
}
