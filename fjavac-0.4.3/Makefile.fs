
bin=/usr/local/bin


all: aot install

aot:
	mono --aot bin/fslib10ntc.dll
	mono --aot bin/mllib10ntc.dll
	mono --aot bin/FSharp.Compiler10ntc.dll
	mono --aot bin/fsi10ntc.exe
	mono --aot bin/fscp10ntc.exe
	mono --aot bin/fslexp10ntc.exe

install:
	gacutil -i bin/fslib10ntc.dll
	gacutil -i bin/mllib10ntc.dll
	gacutil -i bin/FSharp.Compiler10ntc.dll

	cp bin/fslib10ntc.dll* $(bin)
	cp bin/mllib10ntc.dll* $(bin)
	cp bin/FSharp.Compiler10ntc.dll* $(bin)
	cp bin/fsi10ntc.exe* $(bin)
	cp bin/fscp10ntc.exe $(bin)
	cp bin/fslexp10ntc.exe* $(bin)

	echo -e '#!/bin/sh\nfscp10ntc.exe --gnu-style-errors 0 $$*' > $(bin)/fsc
	chmod +x $(bin)/fsc

	ln -fs fsi10ntc.exe $(bin)/fsi
	ln -fs fslexp10ntc.exe $(bin)/fslex
