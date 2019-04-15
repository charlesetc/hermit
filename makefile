test:
	@dune runtest && bash -c "echo -e \"\e[32mTests passed!\e[0m\""

run: hermit.exe
	@dune exec hermit_exe.exe

hermit.exe: bin/*.ml lib/*.ml
	@dune build hermit_exe.exe
