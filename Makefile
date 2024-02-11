build: test.s
	nasm -f elf64 test.s -o build/test.o
	gcc -o build/test build/test.o

run: build
	./build/test