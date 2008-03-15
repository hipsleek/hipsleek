class RTC {
	static long curColor = 1;
	static long colorGen = 3;

	/* stack of live colors */
	static int size = 0;
	static long callStack[] = new long[1024];

	// before calling "traverse", call this method
	// to set curColor to new correct value.
	static void call() {
		if (size == callStack.length) {
			/*
			  Resize if there's not enough space.
			 */
			int newSize = callStack.length << 1;
			long tmp[] = new long[newSize];
			for (int i = 0; i < callStack.length; i++) {
				tmp[i] = callStack[i];
			}
			callStack = tmp;
		}

		callStack[size++] = curColor;

		curColor = colorGen++;
	}

	// call after "traverse" of the postcondition
	static void ret() {
		curColor = callStack[--size];
	}
}
